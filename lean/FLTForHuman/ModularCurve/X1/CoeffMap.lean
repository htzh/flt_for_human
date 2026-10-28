/-
The coefficient-map dictionary over the `q`-expansion function fields.

Seven headlines, one theory: the base-change dictionary for
`ModularCurve.coeffMap` acting on `ModularCurve.qExpFunctionFieldC K Γ`.

* `laurentBaseChange_qExpFunctionFieldC_eq` (92): base change of the `ℚ` field is the
  `L` field.
* `linearIndependent_coeffMap_comp_of_linearIndependent` (45): `LinearIndependent`
  transports along `coeffMap (algebraMap κ k)`.
* `isIntegral_adjoin_of_isIntegral_adjoin_coeffMap` (98): integrality over
  `Algebra.adjoin k {j}` reflects from `L` to `k` along `coeffMap σ`.
* `mem_qExpFunctionFieldC_rat_iff_mem_intFormRatiosC` (120): over `ℚ` the field is
  exactly the set of ratios.
* `exists_modularForm_mul_qExpansion_eq_of_mem_laurentBaseChange_qExpFunctionFieldC_of_T_mem`
  (211): every element of the base-changed field is a ratio of two modular forms.
* `finiteDimensional_and_finrank_adjoin_le_of_eq_coeffMap` (314) and
  `existsUnique_algEquiv_qExpFunctionFieldC_coe_apply_eq_coeffMap` (468): the
  algEquiv dictionary and its finrank inequality.

The seven rows share the 95-line `linearIndependent_coeffMap`/`coeffMap_mem`
prelude, written once here in `ModularCurve.QExpAutBaseChange` and used by both
the 468 and the 314 blocks.  `coeffMap_intSeriesC` is *not* restated: the port
already has it, public, in `ModularCurve/X1/DiamondCorrespondence.lean`; the
general-`φ` form the two blocks need is a `private` helper here.

The pin's `set_option`s (`autoImplicit`, the linters, `synthInstance.maxHeartbeats
1600000`) and its `attribute [-simp] ModularCurve.qExpandAlgHomC_apply
ModularCurve.jqNModC_one` preludes are not transcribed: the project caps and the
port's own `qExpandAlgHomC`/`jqNModC_one` govern.  `p2m_export`/`p2m_open`/
`p2m_reactivate` are pin plumbing; the port uses plain namespaces.

FLT provenance, pinned `aa2d8b3`:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_existsUnique_algEquiv_qExpFunctionFieldC_coe_apply_eq_coeffMap.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_finiteDimensional_and_finrank_adjoin_le_of_eq_coeffMap.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_exists_modularForm_mul_qExpansion_eq_of_mem_laurentBaseChange_qExpFunctionFieldC_of_T_mem.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_mem_qExpFunctionFieldC_rat_iff_mem_intFormRatiosC.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_isIntegral_adjoin_of_isIntegral_adjoin_coeffMap.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_laurentBaseChange_qExpFunctionFieldC_eq.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_linearIndependent_coeffMap_comp_of_linearIndependent.lean

spec-pin: Theorems/Thm_ModularCurve_existsUnique_algEquiv_qExpFunctionFieldC_coe_apply_eq_coeffMap.lean
spec-pin: P2M/Sol/S_ModularCurve_existsUnique_algEquiv_qExpFunctionFieldC_coe_apply_eq_coeffMap.lean
spec-pin: Theorems/Thm_ModularCurve_finiteDimensional_and_finrank_adjoin_le_of_eq_coeffMap.lean
spec-pin: P2M/Sol/S_ModularCurve_finiteDimensional_and_finrank_adjoin_le_of_eq_coeffMap.lean
spec-pin: Theorems/Thm_ModularCurve_exists_modularForm_mul_qExpansion_eq_of_mem_laurentBaseChange_qExpFunctionFieldC_of_T_mem.lean
spec-pin: P2M/Sol/S_ModularCurve_exists_modularForm_mul_qExpansion_eq_of_mem_laurentBaseChange_qExpFunctionFieldC_of_T_mem.lean
spec-pin: Theorems/Thm_ModularCurve_mem_qExpFunctionFieldC_rat_iff_mem_intFormRatiosC.lean
spec-pin: P2M/Sol/S_ModularCurve_mem_qExpFunctionFieldC_rat_iff_mem_intFormRatiosC.lean
spec-pin: Theorems/Thm_ModularCurve_isIntegral_adjoin_of_isIntegral_adjoin_coeffMap.lean
spec-pin: P2M/Sol/S_ModularCurve_isIntegral_adjoin_of_isIntegral_adjoin_coeffMap.lean
spec-pin: Theorems/Thm_ModularCurve_laurentBaseChange_qExpFunctionFieldC_eq.lean
spec-pin: P2M/Sol/S_ModularCurve_laurentBaseChange_qExpFunctionFieldC_eq.lean
spec-pin: Theorems/Thm_ModularCurve_linearIndependent_coeffMap_comp_of_linearIndependent.lean
spec-pin: P2M/Sol/S_ModularCurve_linearIndependent_coeffMap_comp_of_linearIndependent.lean
-/

import FLTForHuman.ModularCurve.X1.DiamondCorrespondence
import FLTForHuman.ModularCurve.Defs.Jq

set_option autoImplicit false

noncomputable section

open ModularCurve IntermediateField HahnSeries Module Polynomial
open scoped MatrixGroups

namespace ModularCurve

/- The pin's `attribute [local instance 2000] Algebra.toSMul Algebra.toModule`: with
mathlib `v4.34` the pointwise `HahnSeries.instSMul` wins the default `SMul` search on
`LaurentSeries`, while the `IntermediateField` coercion lemmas speak `Algebra.toSMul`.
Giving the `Algebra` projections priority 2000 makes the two spellings one. -/
attribute [local instance 2000] Algebra.toSMul Algebra.toModule

/-! ## The shared prelude: `coeffMap` on the `q`-expansion function fields -/

namespace QExpAutBaseChange

variable {K₀ K : Type*} [Field K₀] [Field K] (φ : K₀ →+* K) (Γ : Subgroup SL(2, ℤ))

theorem coeff_smul' {L : Type*} [Field L] (r : L) (x : LaurentSeries L) (n : ℤ) :
    (r • x).coeff n = r * x.coeff n := by
  rw [Algebra.smul_def, algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single_zero_mul]

/-- The general-`φ` form of `coeffMap_intSeriesC` (the port's public witness in
`X1/DiamondCorrespondence.lean` is the `ℚ → ℂ` specialisation; it is imported, not
restated). -/
private theorem coeffMap_intSeriesC_gen (p : PowerSeries ℤ) :
    coeffMap φ (intSeriesC K₀ p) = intSeriesC K p := by
  rw [intSeriesC, intSeriesC, coeffMap_ofPowerSeries, ← RingHom.comp_apply (PowerSeries.map φ),
    ← PowerSeries.map_comp, RingHom.ext_int (φ.comp (Int.castRingHom K₀)) (Int.castRingHom K)]

include φ in
theorem intSeriesC_ne_zero_iff (p : PowerSeries ℤ) :
    intSeriesC K p ≠ 0 ↔ intSeriesC K₀ p ≠ 0 := by
  rw [← coeffMap_intSeriesC_gen φ]
  refine ⟨fun h h0 => h (by rw [h0, map_zero]), fun h h0 => h ?_⟩
  exact coeffMap_injective φ.injective (h0.trans (map_zero _).symm)

theorem coeffMap_algebraMap' (c : K₀) :
    coeffMap φ (algebraMap K₀ (LaurentSeries K₀) c) = algebraMap K (LaurentSeries K) (φ c) := by
  rw [algebraMap_laurentSeries_eq_single, coeffMap_single, ← algebraMap_laurentSeries_eq_single]

theorem intFormRatiosC_eq_image :
    intFormRatiosC K Γ = coeffMap φ '' intFormRatiosC K₀ Γ := by
  ext y
  constructor
  · rintro ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩
    refine ⟨intSeriesC K₀ pf / intSeriesC K₀ pg,
      ⟨k, f, g, pf, pg, hf, hg, (intSeriesC_ne_zero_iff φ pg).mp hg0, rfl⟩, ?_⟩
    rw [map_div₀, coeffMap_intSeriesC_gen, coeffMap_intSeriesC_gen]
  · rintro ⟨x, ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩, rfl⟩
    refine ⟨k, f, g, pf, pg, hf, hg, (intSeriesC_ne_zero_iff φ pg).mpr hg0, ?_⟩
    rw [map_div₀, coeffMap_intSeriesC_gen, coeffMap_intSeriesC_gen]

theorem coeffMap_mem {x : LaurentSeries K₀} (hx : x ∈ qExpFunctionFieldC K₀ Γ) :
    coeffMap φ x ∈ qExpFunctionFieldC K Γ := by
  let T : Subfield (LaurentSeries K₀) := (qExpFunctionFieldC K Γ).toSubfield.comap (coeffMap φ)
  have hgen : intFormRatiosC K₀ Γ ⊆ (T : Set (LaurentSeries K₀)) := by
    intro y hy
    change coeffMap φ y ∈ qExpFunctionFieldC K Γ
    apply intFormRatiosC_subset K Γ
    rw [intFormRatiosC_eq_image φ Γ]
    exact ⟨y, hy, rfl⟩
  have hconst : Set.range (algebraMap K₀ (LaurentSeries K₀)) ⊆ (T : Set (LaurentSeries K₀)) := by
    rintro y ⟨c, rfl⟩
    change coeffMap φ (algebraMap K₀ (LaurentSeries K₀) c) ∈ qExpFunctionFieldC K Γ
    rw [coeffMap_algebraMap']
    exact (qExpFunctionFieldC K Γ).algebraMap_mem _
  have hle : (qExpFunctionFieldC K₀ Γ).toSubfield ≤ T := by
    rw [qExpFunctionFieldC, IntermediateField.adjoin_toSubfield]
    exact Subfield.closure_le.mpr (Set.union_subset hconst hgen)
  exact hle hx

abbrev E₀ : Type _ := ↥(qExpFunctionFieldC K₀ Γ)

abbrev E : Type _ := ↥(qExpFunctionFieldC K Γ)

def iota : E₀ (K₀ := K₀) Γ →+* E (K := K) Γ where
  toFun y := ⟨coeffMap φ y, coeffMap_mem φ Γ y.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _a _b := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' _a _b := Subtype.ext (map_add _ _ _)

@[simp] theorem coe_iota (y : E₀ (K₀ := K₀) Γ) :
    ((iota φ Γ y : E (K := K) Γ) : LaurentSeries K) = coeffMap φ y := rfl

theorem iota_injective : Function.Injective (iota φ Γ) := fun _a _b h =>
  Subtype.ext (coeffMap_injective φ.injective (congrArg Subtype.val h))

theorem iota_smul (c : K₀) (y : E₀ (K₀ := K₀) Γ) : iota φ Γ (c • y) = φ c • iota φ Γ y := by
  apply Subtype.ext
  rw [coe_iota, IntermediateField.coe_smul, IntermediateField.coe_smul, Algebra.smul_def,
    Algebra.smul_def, map_mul, coeffMap_algebraMap', coe_iota]

theorem linearIndependent_coeffMap {ι : Type*} {v : ι → LaurentSeries K₀}
    (hv : LinearIndependent K₀ v) :
    LinearIndependent K (fun i => coeffMap φ (v i)) := by
  classical
  let _ : Algebra K₀ K := φ.toAlgebra
  have hφ : ∀ c : K₀, algebraMap K₀ K c = φ c := fun _ => rfl
  rw [linearIndependent_iff']
  intro s c hsum i hi
  let W : Submodule K₀ K := Submodule.span K₀ (Set.range fun j : s => c j)
  have : Module.Finite K₀ W := Module.Finite.span_of_finite K₀ (Set.finite_range _)
  let b := Module.finBasis K₀ W
  have hcW : ∀ j : s, c j ∈ W := fun j => Submodule.subset_span ⟨j, rfl⟩
  let a : s → Fin (Module.finrank K₀ W) → K₀ := fun j l => b.repr ⟨c j, hcW j⟩ l
  have hca : ∀ j : s, c j = ∑ l, a j l • (b l : K) := by
    intro j
    have h1 := b.sum_repr ⟨c j, hcW j⟩
    have h2 := congrArg (Submodule.subtype W) h1
    rw [map_sum] at h2
    simp only [Submodule.subtype_apply, Submodule.coe_smul] at h2
    exact h2.symm
  have hcoeff : ∀ n : ℤ, ∑ j ∈ s, c j * φ ((v j).coeff n) = 0 := by
    intro n
    have := congrArg (fun x : LaurentSeries K => x.coeff n) hsum
    simpa [HahnSeries.coeff_sum, coeff_smul', coeffMap_coeff] using this
  have hbi : LinearIndependent K₀ (fun l' => (b l' : K)) :=
    b.linearIndependent.map' W.subtype (Submodule.ker_subtype W)
  have hv' : LinearIndependent K₀ (fun j : s => v j) := hv.comp _ Subtype.val_injective
  have hrel : ∀ l, ∑ j : s, a j l • v j = 0 := by
    intro l
    ext n
    have h1 : ∑ l', (∑ j : s, a j l' * (v j).coeff n) • (b l' : K) = 0 := by
      have h0 := hcoeff n
      rw [← Finset.sum_coe_sort] at h0
      simp_rw [hca, Finset.sum_mul] at h0
      rw [Finset.sum_comm] at h0
      rw [← h0]
      refine Finset.sum_congr rfl fun l' _ => ?_
      rw [Finset.sum_smul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Algebra.smul_def, Algebra.smul_def, map_mul, hφ, hφ]; ring
    have := Fintype.linearIndependent_iff.mp hbi (fun l' => ∑ j : s, a j l' * (v j).coeff n) h1 l
    rw [HahnSeries.coeff_sum]
    simpa [coeff_smul'] using this
  have ha : ∀ (j : s) l, a j l = 0 := fun j l =>
    Fintype.linearIndependent_iff.mp hv' (fun j => a j l) (hrel l) j
  rw [show c i = c (⟨i, hi⟩ : s) from rfl, hca]
  simp [ha]

end QExpAutBaseChange

/-! ## Row 92 — base change of the `q`-expansion function field -/

namespace BCEqProof

variable (L : Type*) [Field L] [Algebra ℚ L] (Γ : Subgroup SL(2, ℤ))

theorem image_intFormRatiosC : ⇑(coeffEmb L) '' intFormRatiosC ℚ Γ = intFormRatiosC L Γ := by
  have hinj : Function.Injective (coeffEmb L) := coeffEmb_injective L
  ext x
  constructor
  · rintro ⟨y, ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩, rfl⟩
    refine ⟨k, f, g, pf, pg, hf, hg, ?_, ?_⟩
    · rw [← coeffEmb_intSeriesC L]
      exact (map_ne_zero_iff _ hinj).mpr hg0
    · rw [map_div₀, coeffEmb_intSeriesC, coeffEmb_intSeriesC]
  · rintro ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩
    refine ⟨intSeriesC ℚ pf / intSeriesC ℚ pg, ⟨k, f, g, pf, pg, hf, hg, ?_, rfl⟩, ?_⟩
    · intro h0
      apply hg0
      rw [← coeffEmb_intSeriesC L, h0, map_zero]
    · rw [map_div₀, coeffEmb_intSeriesC, coeffEmb_intSeriesC]

theorem coeffEmb_mem_adjoin (S : Set (LaurentSeries ℚ)) {x : LaurentSeries ℚ}
    (hx : x ∈ IntermediateField.adjoin ℚ S) :
    coeffEmb L x ∈ IntermediateField.adjoin L (⇑(coeffEmb L) '' S) := by
  induction hx using IntermediateField.adjoin_induction with
  | mem x hx => exact IntermediateField.subset_adjoin L _ ⟨x, hx, rfl⟩
  | algebraMap c =>
    rw [algebraMap_laurentSeries_eq_single, show coeffEmb L (HahnSeries.single 0 c) =
      HahnSeries.single 0 (algebraMap ℚ L c) from coeffMap_single _ _ _, ← algebraMap_laurentSeries_eq_single]
    exact IntermediateField.algebraMap_mem _ _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | inv x _ hx => rw [map_inv₀]; exact inv_mem hx
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

end BCEqProof

theorem laurentBaseChange_qExpFunctionFieldC_eq
    (L : Type*) [Field L] [Algebra ℚ L] (Γ : Subgroup SL(2, ℤ)) :
    laurentBaseChange L (qExpFunctionFieldC ℚ Γ) = qExpFunctionFieldC L Γ := by
  apply le_antisymm
  · show IntermediateField.adjoin L
      (⇑(coeffEmb L) '' (qExpFunctionFieldC ℚ Γ : Set (LaurentSeries ℚ))) ≤ _
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨x, hx, rfl⟩
    have h := BCEqProof.coeffEmb_mem_adjoin L (intFormRatiosC ℚ Γ) hx
    rw [BCEqProof.image_intFormRatiosC] at h
    exact h
  · show IntermediateField.adjoin L (intFormRatiosC L Γ) ≤ _
    rw [IntermediateField.adjoin_le_iff, ← BCEqProof.image_intFormRatiosC L Γ]
    rintro _ ⟨x, hx, rfl⟩
    exact coeffEmb_mem_laurentBaseChange L (intFormRatiosC_subset ℚ Γ hx)

/-! ## Row 45 — `LinearIndependent` transports along `coeffMap` -/

theorem linearIndependent_coeffMap_comp_of_linearIndependent
    (κ : Type*) [Field κ] (k : Type*) [Field k] [Algebra κ k]
    {n : ℕ} (f : Fin n → LaurentSeries κ) (hf : LinearIndependent κ f) :
    LinearIndependent k (⇑(coeffMap (algebraMap κ k)) ∘ f) := by
  classical
  set g : κ →+* k := algebraMap κ k with hg
  rw [Fintype.linearIndependent_iff] at hf ⊢
  intro c hc i₀
  let B := Module.Basis.ofVectorSpace κ k
  have hcomb : ∀ j, ∑ i, (B.repr (c i) j) • f i = 0 := by
    intro j
    ext m
    have hm : ∑ i, ((f i).coeff m) • c i = 0 := by
      have h0 := congrArg (fun x : LaurentSeries k => x.coeff m) hc
      simp only [HahnSeries.coeff_zero, HahnSeries.coeff_sum, Function.comp_apply,
        QExpAutBaseChange.coeff_smul', coeffMap_coeff] at h0
      rw [← h0]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.smul_def, mul_comm]
    have hj := congrArg (fun x : k => B.repr x j) hm
    simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finsupp.coe_smul, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, map_zero, Finsupp.coe_zero, Pi.zero_apply] at hj
    rw [HahnSeries.coeff_sum, HahnSeries.coeff_zero]
    simp only [QExpAutBaseChange.coeff_smul']
    rw [← hj]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hzero : ∀ j, B.repr (c i₀) j = 0 := fun j => hf _ (hcomb j) i₀
  have hrepr : B.repr (c i₀) = 0 := Finsupp.ext hzero
  simpa using congrArg B.repr.symm hrepr

/-! ## Row 120 — over `ℚ` the field is the set of ratios -/

namespace RatioE96

open UpperHalfPlane

variable {Γ : Subgroup SL(2, ℤ)} (hΓ : (1 : ℝ) ∈ ((Γ : Subgroup (GL (Fin 2) ℝ))).strictPeriods)

local notation "Γ'" => ((Γ : Subgroup (GL (Fin 2) ℝ)))

include hΓ in
theorem analytic {k : ℤ} (f : ModularForm Γ' k) : AnalyticAt ℂ (cuspFunction 1 (⇑f)) 0 :=
  ModularFormClass.analyticAt_cuspFunction_zero f one_pos hΓ

include hΓ in
theorem isIntegralQExp_mul {k₁ k₂ : ℤ} (f : ModularForm Γ' k₁) (g : ModularForm Γ' k₂)
    {pf pg : PowerSeries ℤ} (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg) :
    IsIntegralQExp (⇑(f.mul g)) (pf * pg) := by
  unfold IsIntegralQExp at *
  rw [map_mul, hf, hg, ModularForm.coe_mul, qExpansion_mul (analytic hΓ f) (analytic hΓ g)]

include hΓ in
theorem isIntegralQExp_add {k : ℤ} (f g : ModularForm Γ' k)
    {pf pg : PowerSeries ℤ} (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg) :
    IsIntegralQExp (⇑(f + g)) (pf + pg) := by
  unfold IsIntegralQExp at *
  rw [map_add, hf, hg, FunLike.coe_add, qExpansion_add (analytic hΓ f) (analytic hΓ g)]

include hΓ in
theorem isIntegralQExp_intCast_smul_one (a : ℤ) :
    IsIntegralQExp (⇑(((a : ℂ)) • (1 : ModularForm Γ' 0))) (PowerSeries.C a) := by
  unfold IsIntegralQExp
  rw [FunLike.coe_smul, ModularForm.one_coe_eq_one,
    qExpansion_smul (by rw [← ModularForm.one_coe_eq_one (Γ := Γ')]; exact analytic hΓ (1 : ModularForm Γ' 0)),
    qExpansion_one, PowerSeries.map_C]
  ext n
  simp [Algebra.smul_def]

theorem intSeriesC_ne_zero_iff (p : PowerSeries ℤ) : intSeriesC ℚ p ≠ 0 ↔ p ≠ 0 := by
  rw [intSeriesC, Ne, Ne, not_iff_not]
  constructor
  · intro h
    apply PowerSeries.map_injective (Int.castRingHom ℚ) Int.cast_injective
    rw [map_zero]
    exact HahnSeries.ofPowerSeries_injective (h.trans (map_zero _).symm)
  · rintro rfl; simp

theorem intSeriesC_add (K : Type*) [Field K] (p p' : PowerSeries ℤ) :
    intSeriesC K (p + p') = intSeriesC K p + intSeriesC K p' := by
  simp [intSeriesC]

include hΓ in
theorem exists_intermediateField :
    ∃ S : IntermediateField ℚ (LaurentSeries ℚ), (S : Set (LaurentSeries ℚ)) = intFormRatiosC ℚ Γ := by
  classical
  refine ⟨{ carrier := intFormRatiosC ℚ Γ
            mul_mem' := ?_, one_mem' := one_mem_intFormRatiosC ℚ Γ, add_mem' := ?_,
            zero_mem' := ?_, algebraMap_mem' := ?_, inv_mem' := ?_ }, rfl⟩
  · rintro _ _ ⟨k₁, f₁, g₁, pf₁, pg₁, hf₁, hg₁, h₁, rfl⟩ ⟨k₂, f₂, g₂, pf₂, pg₂, hf₂, hg₂, h₂, rfl⟩
    refine ⟨k₁ + k₂, f₁.mul f₂, g₁.mul g₂, pf₁ * pf₂, pg₁ * pg₂, isIntegralQExp_mul hΓ f₁ f₂ hf₁ hf₂,
      isIntegralQExp_mul hΓ g₁ g₂ hg₁ hg₂, ?_, ?_⟩
    · rw [intSeriesC_mul]; exact mul_ne_zero h₁ h₂
    · rw [intSeriesC_mul, intSeriesC_mul, div_mul_div_comm]
  · rintro _ _ ⟨k₁, f₁, g₁, pf₁, pg₁, hf₁, hg₁, h₁, rfl⟩ ⟨k₂, f₂, g₂, pf₂, pg₂, hf₂, hg₂, h₂, rfl⟩
    refine ⟨k₁ + k₂, f₁.mul g₂ + g₁.mul f₂, g₁.mul g₂, pf₁ * pg₂ + pg₁ * pf₂, pg₁ * pg₂,
      isIntegralQExp_add hΓ _ _ (isIntegralQExp_mul hΓ f₁ g₂ hf₁ hg₂) (isIntegralQExp_mul hΓ g₁ f₂ hg₁ hf₂),
      isIntegralQExp_mul hΓ g₁ g₂ hg₁ hg₂, ?_, ?_⟩
    · rw [intSeriesC_mul]; exact mul_ne_zero h₁ h₂
    · rw [intSeriesC_add, intSeriesC_mul, intSeriesC_mul, intSeriesC_mul, div_add_div _ _ h₁ h₂]
  · refine ⟨0, 0, 1, 0, 1, ?_, ?_, by simp, by simp⟩
    · show IsIntegralQExp (⇑(0 : ModularForm Γ' 0)) 0
      rw [FunLike.coe_zero]; exact isIntegralQExp_zero
    · show IsIntegralQExp (⇑(1 : ModularForm Γ' 0)) 1
      rw [ModularForm.one_coe_eq_one]; exact isIntegralQExp_one
  · intro c
    refine ⟨0, ((c.num : ℂ)) • (1 : ModularForm Γ' 0), ((c.den : ℤ) : ℂ) • (1 : ModularForm Γ' 0),
      PowerSeries.C c.num, PowerSeries.C (c.den : ℤ), isIntegralQExp_intCast_smul_one hΓ c.num,
      isIntegralQExp_intCast_smul_one hΓ c.den, ?_, ?_⟩
    · rw [DiamondCorrespondence.intSeriesC_C]
      exact HahnSeries.C_ne_zero (by exact_mod_cast c.den_nz)
    · rw [DiamondCorrespondence.intSeriesC_C, DiamondCorrespondence.intSeriesC_C, ← map_div₀]
      push_cast
      rw [Rat.num_div_den, HahnSeries.algebraMap_apply']
      simp
  · rintro _ ⟨k, f, g, pf, pg, hf, hg, h, rfl⟩
    by_cases hpf : intSeriesC ℚ pf = 0
    · rw [hpf, zero_div, inv_zero]
      refine ⟨0, 0, 1, 0, 1, ?_, ?_, by simp, by simp⟩
      · show IsIntegralQExp (⇑(0 : ModularForm Γ' 0)) 0
        rw [FunLike.coe_zero]; exact isIntegralQExp_zero
      · show IsIntegralQExp (⇑(1 : ModularForm Γ' 0)) 1
        rw [ModularForm.one_coe_eq_one]; exact isIntegralQExp_one
    · exact ⟨k, g, f, pg, pf, hg, hf, hpf, (inv_div _ _)⟩

end RatioE96

theorem mem_qExpFunctionFieldC_rat_iff_mem_intFormRatiosC
    (Γ : Subgroup SL(2, ℤ)) (hΓ : (1 : ℝ) ∈ ((Γ : Subgroup (GL (Fin 2) ℝ))).strictPeriods)
    (x : LaurentSeries ℚ) :
    x ∈ qExpFunctionFieldC ℚ Γ ↔ x ∈ intFormRatiosC ℚ Γ := by
  obtain ⟨S, hS⟩ := RatioE96.exists_intermediateField hΓ
  have hle : qExpFunctionFieldC ℚ Γ ≤ S :=
    IntermediateField.adjoin_le_iff.mpr (by rw [hS])
  constructor
  · intro hx
    have := hle hx
    rwa [← SetLike.mem_coe, hS] at this
  · intro hx
    exact intFormRatiosC_subset ℚ Γ hx

/-! ## Row 98 — integrality reflects along `coeffMap` -/

theorem isIntegral_adjoin_of_isIntegral_adjoin_coeffMap {k L : Type*} [Field k]
    [Field L] (σ : k →+* L) (j x : LaurentSeries k)
    (h : IsIntegral (Algebra.adjoin L ({coeffMap σ j} : Set (LaurentSeries L))) (coeffMap σ x)) :
    IsIntegral (Algebra.adjoin k ({j} : Set (LaurentSeries k))) x := by
  classical
  let _ : Algebra k L := σ.toAlgebra
  obtain ⟨π, hπ⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap k L)
    (LinearMap.ker_eq_bot.mpr (algebraMap k L).injective)
  have hπσ : ∀ a : k, π (σ a) = a := fun a => by
    have h__af := LinearMap.congr_fun hπ a
    simp at h__af
    exact h__af
  let Pr : LaurentSeries L →+ LaurentSeries k :=
    { toFun := fun Z => Z.map π
      map_zero' := by ext n; simp
      map_add' := fun Z Z' => by ext n; simp }
  have hPr_coeff : ∀ (Z : LaurentSeries L) (n : ℤ), (Pr Z).coeff n = π (Z.coeff n) :=
    fun Z n => rfl
  have hPr_mul : ∀ (c : L) (z : LaurentSeries k),
      Pr (algebraMap L (LaurentSeries L) c * coeffMap σ z) =
        algebraMap k (LaurentSeries k) (π c) * z := by
    intro c z
    ext n
    rw [hPr_coeff, algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single,
      HahnSeries.coeff_single_zero_mul, HahnSeries.coeff_single_zero_mul, coeffMap_coeff, mul_comm c,
      show σ (z.coeff n) * c = (z.coeff n) • c from (Algebra.smul_def (z.coeff n) c).symm,
      map_smul, smul_eq_mul, mul_comm]
  set J := coeffMap σ j with hJ
  set X := coeffMap σ x with hX
  obtain ⟨P, hPm, hPev⟩ := h
  set n := P.natDegree with hn
  have hrep : ∀ i : ℕ, ∃ p : Polynomial L,
      Polynomial.aeval J p = ((P.coeff i : _) : LaurentSeries L) := fun i =>
    (AlgHom.mem_range _).mp ((Algebra.adjoin_singleton_eq_range_aeval L J).le (P.coeff i).2)
  choose p hp using hrep
  let a : ℕ → LaurentSeries k := fun i => Pr ((P.coeff i : _) : LaurentSeries L)
  have ha_eq : ∀ i, a i = ∑ m ∈ Finset.range ((p i).natDegree + 1),
      algebraMap k (LaurentSeries k) (π ((p i).coeff m)) * j ^ m := by
    intro i
    show Pr _ = _
    rw [← hp i, Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range, map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [show J ^ m = coeffMap σ (j ^ m) from (map_pow _ _ _).symm, hPr_mul]
  have ha_mem : ∀ i, a i ∈ Algebra.adjoin k ({j} : Set (LaurentSeries k)) := by
    intro i
    rw [ha_eq]
    exact Subalgebra.sum_mem _ fun m _ => Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _)
      (Subalgebra.pow_mem _ (Algebra.self_mem_adjoin_singleton k j) m)
  have ha_mul : ∀ i, Pr (((P.coeff i : _) : LaurentSeries L) * X ^ i) = a i * x ^ i := by
    intro i
    rw [ha_eq, ← hp i, Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range, Finset.sum_mul,
      map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [mul_assoc, mul_assoc,
      show J ^ m * X ^ i = coeffMap σ (j ^ m * x ^ i) by rw [map_mul, map_pow, map_pow],
      hPr_mul]
  have ha_top : a n = 1 := by
    show Pr _ = 1
    have h1 : ((P.coeff n : _) : LaurentSeries L) =
        algebraMap L (LaurentSeries L) 1 * coeffMap σ 1 := by
      rw [map_one, map_one, one_mul, show P.coeff n = 1 from hPm.coeff_natDegree]
      rfl
    rw [h1, hPr_mul, show π 1 = 1 by simpa using hπσ 1, map_one, one_mul]
  have hrel : ∑ i ∈ Finset.range (n + 1), a i * x ^ i = 0 := by
    have h0 : Pr (Polynomial.eval₂ (algebraMap _ (LaurentSeries L)) X P) = 0 := by
      rw [hPev, map_zero]
    rw [Polynomial.eval₂_eq_sum_range, map_sum] at h0
    rw [← h0]
    exact Finset.sum_congr rfl fun i _ => (ha_mul i).symm
  let A : Subalgebra k (LaurentSeries k) := Algebra.adjoin k ({j} : Set (LaurentSeries k))
  let b : Fin n → A := fun i => ⟨a i, ha_mem i⟩
  let Q : Polynomial A :=
    ∑ i : Fin n, (Polynomial.C (b i) : Polynomial A) * (Polynomial.X : Polynomial A) ^ (i : ℕ)
  refine ⟨Polynomial.X ^ n + Q, Polynomial.monic_X_pow_add (Polynomial.degree_sum_fin_lt b), ?_⟩
  rw [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finsetSum]
  simp only [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow]
  rw [Finset.sum_range_succ, ha_top, one_mul] at hrel
  rw [← hrel, add_comm, Finset.sum_range]
  rfl

/-! ## Row 211 — every base-changed element is a ratio of modular forms -/

namespace RatioFieldOfGroup

open UpperHalfPlane

variable {Γ : Subgroup SL(2, ℤ)}

abbrev qL {k : ℤ} (f : ModularForm Γ k) : LaurentSeries ℂ :=
  ((qExpansion 1 (f : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)

theorem one_mem_strictPeriods (hT : ModularGroup.T ∈ Γ) :
    (1 : ℝ) ∈ (Γ : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem hT]
  exact AddSubgroup.mem_zmultiples _

variable (hT : ModularGroup.T ∈ Γ)
include hT

theorem qL_ne_zero {k : ℤ} (f : ModularForm Γ k) (hf : f ≠ 0) : qL f ≠ 0 := by
  intro h
  apply hf
  rw [← ModularForm.qExpansion_eq_zero_iff one_pos (one_mem_strictPeriods hT)]
  apply (HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℂ))
  simpa [qL] using h

theorem qL_mul {a b : ℤ} (f : ModularForm Γ a) (g : ModularForm Γ b) : qL (f.mul g) = qL f * qL g := by
  rw [qL, qL, qL, ModularForm.qExpansion_mul one_pos (one_mem_strictPeriods hT),
    PowerSeries.coe_mul]

theorem qL_add {a : ℤ} (f g : ModularForm Γ a) : qL (f + g) = qL f + qL g := by
  simp only [qL, FunLike.coe_add,
    ModularForm.qExpansion_add one_pos (one_mem_strictPeriods hT), PowerSeries.coe_add]

omit hT in
theorem qL_one : qL (1 : ModularForm Γ 0) = 1 := by
  simp only [qL, ModularForm.qExpansion_one, PowerSeries.coe_one]

theorem qL_const (c : ℂ) :
    qL (c • (1 : ModularForm Γ 0)) = algebraMap ℂ (LaurentSeries ℂ) c := by
  rw [qL, FunLike.coe_smul,
    ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods hT), ModularForm.qExpansion_one,
    Algebra.smul_def, mul_one, HahnSeries.algebraMap_apply']

omit hT in
theorem one_ne_zero' : (1 : ModularForm Γ 0) ≠ 0 := by
  intro h
  have := congrArg (fun F : ModularForm Γ 0 => (F : ℍ → ℂ) UpperHalfPlane.I) h
  simp [ModularForm.one_coe_eq_one] at this

theorem mul_ne_zero' {a b : ℤ} (f : ModularForm Γ a) (g : ModularForm Γ b) (hf : f ≠ 0) (hg : g ≠ 0) :
    f.mul g ≠ 0 := by
  intro hfg
  have h := congrArg (qL (Γ := Γ)) hfg
  rw [qL_mul hT] at h
  have h0 : qL (0 : ModularForm Γ (a + b)) = 0 := by
    simp only [qL, FunLike.coe_zero, UpperHalfPlane.qExpansion_zero (1 : ℝ), PowerSeries.coe_zero]
  rw [h0] at h
  exact (mul_ne_zero (qL_ne_zero hT f hf) (qL_ne_zero hT g hg)) h

omit hT in
variable (Γ) in
def IsRatio (x : LaurentSeries ℂ) : Prop :=
  ∃ (k : ℤ) (g h : ModularForm Γ k), h ≠ 0 ∧ x * qL h = qL g

theorem isRatio_algebraMap (c : ℂ) : IsRatio Γ (algebraMap ℂ (LaurentSeries ℂ) c) :=
  ⟨0, c • 1, 1, one_ne_zero', by rw [qL_one, mul_one, qL_const hT]⟩

theorem isRatio_one : IsRatio Γ 1 := by
  simpa using isRatio_algebraMap hT 1

theorem IsRatio.mul {x y : LaurentSeries ℂ} (hx : IsRatio Γ x) (hy : IsRatio Γ y) :
    IsRatio Γ (x * y) := by
  obtain ⟨a, g, h, hh, hxe⟩ := hx
  obtain ⟨b, g', h', hh', hye⟩ := hy
  refine ⟨a + b, g.mul g', h.mul h', mul_ne_zero' hT h h' hh hh', ?_⟩
  rw [qL_mul hT, qL_mul hT, ← hxe, ← hye]; ring

theorem IsRatio.add {x y : LaurentSeries ℂ} (hx : IsRatio Γ x) (hy : IsRatio Γ y) :
    IsRatio Γ (x + y) := by
  obtain ⟨a, g, h, hh, hxe⟩ := hx
  obtain ⟨b, g', h', hh', hye⟩ := hy
  refine ⟨a + b, g.mul h' + ModularForm.mcast (add_comm b a) (g'.mul h), h.mul h',
    mul_ne_zero' hT h h' hh hh', ?_⟩
  have hc : qL (ModularForm.mcast (add_comm b a) (g'.mul h)) = qL g' * qL h := by
    rw [← qL_mul hT]; simp only [qL, ModularForm.coe_mcast]
  rw [qL_add hT, qL_mul hT, qL_mul hT, hc, ← hxe, ← hye]; ring

theorem IsRatio.neg {x : LaurentSeries ℂ} (hx : IsRatio Γ x) : IsRatio Γ (-x) := by
  have : -x = algebraMap ℂ (LaurentSeries ℂ) (-1) * x := by rw [map_neg, map_one]; ring
  rw [this]
  exact (isRatio_algebraMap hT (-1)).mul hT hx

theorem IsRatio.inv {x : LaurentSeries ℂ} (hx : IsRatio Γ x) : IsRatio Γ x⁻¹ := by
  rcases eq_or_ne x 0 with rfl | hx0
  · simpa using isRatio_algebraMap hT 0
  obtain ⟨a, g, h, hh, hxe⟩ := hx
  have hg : g ≠ 0 := by
    intro hg0
    have : qL g = 0 := by
      simp only [hg0, qL, FunLike.coe_zero, UpperHalfPlane.qExpansion_zero (1 : ℝ),
        PowerSeries.coe_zero]
    rw [this] at hxe
    exact (mul_ne_zero hx0 (qL_ne_zero hT h hh)) hxe
  refine ⟨a, h, g, hg, ?_⟩
  rw [← hxe, mul_comm x, mul_comm x⁻¹, mul_assoc, mul_inv_cancel₀ hx0, mul_one]

omit hT in
theorem coeffEmb_algebraMap (r : ℚ) :
    coeffEmb ℂ (algebraMap ℚ (LaurentSeries ℚ) r) = algebraMap ℂ (LaurentSeries ℂ) (r : ℂ) := by
  rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffEmb,
    coeffMap_single]
  simp

omit hT in
theorem coeffEmb_intSeriesC (p : PowerSeries ℤ) : coeffEmb ℂ (intSeriesC ℚ p) = intSeriesC ℂ p :=
  ModularCurve.coeffEmb_intSeriesC ℂ p

omit hT in
theorem intSeriesC_eq_qL {k : ℤ} {f : ModularForm Γ k} {p : PowerSeries ℤ} (hf : IsIntegralQExp f p) :
    intSeriesC ℂ p = qL f := by
  rw [intSeriesC, hf]

omit hT in
theorem isRatio_coeffEmb_of_mem_intFormRatiosC {y : LaurentSeries ℚ} (hy : y ∈ intFormRatiosC ℚ Γ) :
    IsRatio Γ (coeffEmb ℂ y) := by
  obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ := hy
  have hpg : pg ≠ 0 := by
    rintro rfl
    exact hg0 (intSeriesC_zero ℚ)
  have hgC : intSeriesC ℂ pg ≠ 0 := by
    intro h
    apply hpg
    ext n
    have := congrArg (fun s : LaurentSeries ℂ => s.coeff (n : ℤ)) h
    simp only [intSeriesC, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map, eq_intCast,
      HahnSeries.coeff_zero, Int.cast_eq_zero] at this
    simpa using this
  have hgne : g ≠ 0 := by
    intro h0
    apply hgC
    rw [intSeriesC_eq_qL hg, h0]
    simp only [qL, FunLike.coe_zero, UpperHalfPlane.qExpansion_zero (1 : ℝ), PowerSeries.coe_zero]
  refine ⟨k, f, g, hgne, ?_⟩
  rw [map_div₀, coeffEmb_intSeriesC, coeffEmb_intSeriesC, intSeriesC_eq_qL hf, intSeriesC_eq_qL hg,
    div_mul_cancel₀ _ (by rw [← intSeriesC_eq_qL hg]; exact hgC)]

theorem isRatio_coeffEmb {y : LaurentSeries ℚ} (hy : y ∈ qExpFunctionFieldC ℚ Γ) :
    IsRatio Γ (coeffEmb ℂ y) := by
  change y ∈ Subfield.closure (Set.range (algebraMap ℚ (LaurentSeries ℚ)) ∪ intFormRatiosC ℚ Γ) at hy
  induction hy using Subfield.closure_induction with
  | mem z hz =>
      rcases hz with ⟨r, rfl⟩ | hz
      · rw [coeffEmb_algebraMap]; exact isRatio_algebraMap hT _
      · exact isRatio_coeffEmb_of_mem_intFormRatiosC hz
  | one => simpa using isRatio_one hT
  | add x y _ _ hx hy => simpa using hx.add hT hy
  | neg x _ hx => simpa using hx.neg hT
  | inv x _ hx => simpa using hx.inv hT
  | mul x y _ _ hx hy => simpa using hx.mul hT hy

theorem isRatio_of_mem {x : LaurentSeries ℂ}
    (hx : x ∈ laurentBaseChange ℂ (qExpFunctionFieldC ℚ Γ)) : IsRatio Γ x := by
  rw [mem_laurentBaseChange_iff] at hx
  induction hx using Subfield.closure_induction with
  | mem z hz =>
      rcases hz with ⟨c, rfl⟩ | ⟨y, hy, rfl⟩
      · exact isRatio_algebraMap hT c
      · exact isRatio_coeffEmb hT hy
  | one => exact isRatio_one hT
  | add x y _ _ hx hy => exact hx.add hT hy
  | neg x _ hx => exact hx.neg hT
  | inv x _ hx => exact hx.inv hT
  | mul x y _ _ hx hy => exact hx.mul hT hy

end RatioFieldOfGroup

theorem exists_modularForm_mul_qExpansion_eq_of_mem_laurentBaseChange_qExpFunctionFieldC_of_T_mem
    (Γ : Subgroup SL(2, ℤ)) (hT : ModularGroup.T ∈ Γ) (x : LaurentSeries ℂ)
    (hx : x ∈ laurentBaseChange ℂ (qExpFunctionFieldC ℚ Γ)) :
    ∃ (k : ℤ) (g h : ModularForm Γ k), h ≠ 0 ∧
      x * ((UpperHalfPlane.qExpansion 1 (h : UpperHalfPlane → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
        ((UpperHalfPlane.qExpansion 1 (g : UpperHalfPlane → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) :=
  RatioFieldOfGroup.isRatio_of_mem hT hx


/-! ## Row 314 — the finrank inequality under a `coeffMap` identification -/

namespace QExpDegTransfer

open QExpAutBaseChange

variable {K₀ K : Type*} [Field K₀] [Field K]

section Transfer

variable {φ : K₀ →+* K} {Γ : Subgroup SL(2, ℤ)}
variable (x₀ : qExpFunctionFieldC K₀ Γ) (x : qExpFunctionFieldC K Γ)
  (hx₀ : Transcendental K₀ (x₀ : LaurentSeries K₀))
  (hx : (x : LaurentSeries K) = coeffMap φ (x₀ : LaurentSeries K₀))

local notation "E₀" => (qExpFunctionFieldC K₀ Γ)
local notation "E" => (qExpFunctionFieldC K Γ)

include hx₀ in
theorem transcendental_x₀ : Transcendental K₀ x₀ := by
  have hinj : Function.Injective (algebraMap E₀ (LaurentSeries K₀)) := Subtype.val_injective
  exact (transcendental_algebraMap_iff hinj).mp hx₀

include hx₀ in
theorem linearIndependent_pow_smul {ι : Type*} [Fintype ι] (v : ι → E₀)
    (hv : LinearIndependent (IntermediateField.adjoin K₀ ({x₀} : Set E₀)) v) (N : ℕ) :
    LinearIndependent K₀ (fun p : ι × Fin N => (x₀ : E₀) ^ (p.2 : ℕ) * v p.1) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro a ha
  let A : ι → IntermediateField.adjoin K₀ ({x₀} : Set E₀) := fun i =>
    ⟨∑ m : Fin N, a (i, m) • (x₀ : E₀) ^ (m : ℕ), by
      refine sum_mem fun m _ => IntermediateField.smul_mem _ ?_
      exact pow_mem (IntermediateField.mem_adjoin_simple_self K₀ x₀) _⟩
  have hsum : ∑ i, A i • v i = 0 := by
    have : ∑ i, A i • v i = ∑ p : ι × Fin N, a p • ((x₀ : E₀) ^ (p.2 : ℕ) * v p.1) := by
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun i _ => ?_
      change (∑ m : Fin N, a (i, m) • (x₀ : E₀) ^ (m : ℕ)) * v i = _
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [smul_mul_assoc]
    rw [this]; exact ha
  have hA : ∀ i, A i = 0 := Fintype.linearIndependent_iff.mp hv A hsum
  intro p
  obtain ⟨i, m⟩ := p
  have hAi : ∑ m : Fin N, a (i, m) • ((x₀ : E₀) : LaurentSeries K₀) ^ (m : ℕ) = 0 := by
    have h1 : ((A i : E₀) : LaurentSeries K₀) = 0 := by rw [hA i]; rfl
    have h2 : ((A i : E₀) : LaurentSeries K₀)
        = ∑ m : Fin N, a (i, m) • ((x₀ : E₀) : LaurentSeries K₀) ^ (m : ℕ) := by
      change ((∑ m : Fin N, a (i, m) • (x₀ : E₀) ^ (m : ℕ) : E₀) : LaurentSeries K₀) = _
      rw [AddSubmonoidClass.coe_finsetSum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [IntermediateField.coe_smul, SubmonoidClass.coe_pow]
    rw [← h2]; exact h1
  let P : K₀[X] := ∑ m : Fin N, Polynomial.monomial (m : ℕ) (a (i, m))
  have hP : Polynomial.aeval ((x₀ : E₀) : LaurentSeries K₀) P = 0 := by
    rw [map_sum, ← hAi]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Polynomial.aeval_monomial, Algebra.smul_def]
  have hP0 : P = 0 := by
    by_contra hne
    exact hx₀ ⟨P, hne, hP⟩
  have := congrArg (fun Q : K₀[X] => Q.coeff (m : ℕ)) hP0
  simp only [P, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, Polynomial.coeff_zero] at this
  rw [Finset.sum_eq_single m] at this
  · simpa using this
  · intro m' _ hm'
    rw [ite_eq_right]
    exact fun h => hm' (Fin.ext h)
  · intro h; exact absurd (Finset.mem_univ m) h

include hx₀ hx in
theorem linearIndependent_iota {ι : Type*} [Fintype ι] (v : ι → E₀)
    (hv : LinearIndependent (IntermediateField.adjoin K₀ ({x₀} : Set E₀)) v) :
    LinearIndependent (IntermediateField.adjoin K ({x} : Set E)) (fun i => iota φ Γ (v i)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc
  by_contra hne
  push Not at hne
  obtain ⟨i₀, hi₀⟩ := hne
  have hrep : ∀ i, ∃ r s : K[X], (c i : E) = Polynomial.aeval (x : E) r / Polynomial.aeval (x : E) s := by
    intro i
    exact (IntermediateField.mem_adjoin_simple_iff (F := K) (α := x) (c i : E)).mp (c i).2
  choose r s hrs using hrep
  let s' : ι → K[X] := fun i => if Polynomial.aeval (x : E) (s i) = 0 then 1 else s i
  have hs' : ∀ i, Polynomial.aeval (x : E) (s' i) ≠ 0 := by
    intro i
    simp only [s']
    split_ifs with h
    · rw [map_one]; exact one_ne_zero
    · exact h
  let r' : ι → K[X] := fun i => if Polynomial.aeval (x : E) (s i) = 0 then 0 else r i
  have hrs' : ∀ i, (c i : E) * Polynomial.aeval (x : E) (s' i) = Polynomial.aeval (x : E) (r' i) := by
    intro i
    simp only [s', r']
    split_ifs with h
    · rw [hrs i, h, div_zero, zero_mul, map_zero]
    · rw [hrs i, div_mul_cancel₀ _ h]
  let D : K[X] := ∏ i, s' i
  have hD : Polynomial.aeval (x : E) D ≠ 0 := by
    rw [map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => hs' i
  let P : ι → K[X] := fun i => r' i * ∏ j ∈ Finset.univ.erase i, s' j
  have hPc : ∀ i, Polynomial.aeval (x : E) (P i) = (c i : E) * Polynomial.aeval (x : E) D := by
    intro i
    simp only [P, D]
    rw [map_mul, ← hrs', mul_assoc, ← map_mul, Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  have hrel : ∑ i, Polynomial.aeval (x : E) (P i) • (iota φ Γ (v i) : E) = 0 := by
    have : ∑ i, Polynomial.aeval (x : E) (P i) • (iota φ Γ (v i) : E)
        = Polynomial.aeval (x : E) D * ∑ i, (c i : E) • (iota φ Γ (v i) : E) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hPc, smul_eq_mul, smul_eq_mul]; ring
    rw [this]
    have h0 : ∑ i, (c i : E) • (iota φ Γ (v i) : E) = 0 := by
      have := hc
      simpa only [IntermediateField.smul_def] using this
    rw [h0, mul_zero]
  have hPi₀ : P i₀ ≠ 0 := by
    intro h
    have := hPc i₀
    rw [h, map_zero] at this
    exact mul_ne_zero (fun h0 => hi₀ (ZeroMemClass.coe_eq_zero.mp h0)) hD this.symm
  let N : ℕ := (Finset.univ.sup fun i => (P i).natDegree) + 1
  have hdeg : ∀ i, (P i).natDegree < N := fun i =>
    Nat.lt_succ_of_le (Finset.le_sup (f := fun i => (P i).natDegree) (Finset.mem_univ i))
  have hind₀ := linearIndependent_pow_smul x₀ hx₀ v hv N
  have hind₀' : LinearIndependent K₀
      (fun p : ι × Fin N => (((x₀ : E₀) ^ (p.2 : ℕ) * v p.1 : E₀) : LaurentSeries K₀)) :=
    hind₀.map' (IntermediateField.val E₀).toLinearMap
      (LinearMap.ker_eq_bot_of_injective Subtype.val_injective)
  have hindK := linearIndependent_coeffMap φ hind₀'
  have hexp : ∑ p : ι × Fin N, (P p.1).coeff (p.2 : ℕ) •
      coeffMap φ (((x₀ : E₀) ^ ((p.2 : ℕ)) * v p.1 : E₀) : LaurentSeries K₀) = 0 := by
    have e1 : ∀ i, Polynomial.aeval (x : E) (P i) = ∑ m : Fin N, (P i).coeff (m : ℕ) • (x : E) ^ (m : ℕ) := by
      intro i
      rw [Polynomial.aeval_eq_sum_range' (hdeg i), Finset.sum_range]
    have := congrArg (fun z : E => (z : LaurentSeries K)) hrel
    simp only [IntermediateField.coe_sum, ZeroMemClass.coe_zero] at this
    rw [← this, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [e1, Finset.sum_smul, IntermediateField.coe_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [MulMemClass.coe_mul, SubmonoidClass.coe_pow, map_mul, map_pow, ← hx, smul_eq_mul,
      MulMemClass.coe_mul, IntermediateField.coe_smul, SubmonoidClass.coe_pow, coe_iota, smul_mul_assoc]
  have hzero := Fintype.linearIndependent_iff.mp hindK (fun p => (P p.1).coeff (p.2 : ℕ)) hexp
  apply hPi₀
  ext m
  rw [Polynomial.coeff_zero]
  by_cases hm : m < N
  · exact hzero (i₀, ⟨m, hm⟩)
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le (hdeg i₀) (not_lt.mp hm))

end Transfer

end QExpDegTransfer

theorem finiteDimensional_and_finrank_adjoin_le_of_eq_coeffMap
    {K₀ K : Type*} [Field K₀] [Field K] (φ : K₀ →+* K) (Γ : Subgroup SL(2, ℤ))
    (x₀ : qExpFunctionFieldC K₀ Γ) (x : qExpFunctionFieldC K Γ)
    (hx₀ : Transcendental K₀ (x₀ : LaurentSeries K₀))
    (hx : (x : LaurentSeries K) = coeffMap φ (x₀ : LaurentSeries K₀))
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set (qExpFunctionFieldC K Γ)))
      (qExpFunctionFieldC K Γ)] :
    FiniteDimensional (IntermediateField.adjoin K₀ ({x₀} : Set (qExpFunctionFieldC K₀ Γ)))
        (qExpFunctionFieldC K₀ Γ) ∧
      Module.finrank (IntermediateField.adjoin K₀ ({x₀} : Set (qExpFunctionFieldC K₀ Γ)))
          (qExpFunctionFieldC K₀ Γ) ≤
        Module.finrank (IntermediateField.adjoin K ({x} : Set (qExpFunctionFieldC K Γ)))
          (qExpFunctionFieldC K Γ) := by
  classical
  have : Module.Free (IntermediateField.adjoin K₀ ({x₀} : Set (qExpFunctionFieldC K₀ Γ)))
      (qExpFunctionFieldC K₀ Γ) := Module.Free.of_divisionRing _ _
  set n : ℕ := Module.finrank (IntermediateField.adjoin K ({x} : Set (qExpFunctionFieldC K Γ)))
    (qExpFunctionFieldC K Γ) with hn
  have hbound : ∀ s : Finset (qExpFunctionFieldC K₀ Γ),
      LinearIndependent (IntermediateField.adjoin K₀ ({x₀} : Set (qExpFunctionFieldC K₀ Γ)))
        (fun i : s => (i : qExpFunctionFieldC K₀ Γ)) → s.card ≤ n := by
    intro s hs
    have h := QExpDegTransfer.linearIndependent_iota x₀ x hx₀ hx (fun i : s => (i : qExpFunctionFieldC K₀ Γ)) hs
    have := h.fintype_card_le_finrank
    rwa [Fintype.card_coe] at this
  have hrank : Module.rank (IntermediateField.adjoin K₀ ({x₀} : Set (qExpFunctionFieldC K₀ Γ)))
      (qExpFunctionFieldC K₀ Γ) ≤ n := rank_le hbound
  have hfin : FiniteDimensional (IntermediateField.adjoin K₀ ({x₀} : Set (qExpFunctionFieldC K₀ Γ)))
      (qExpFunctionFieldC K₀ Γ) :=
    Module.rank_lt_aleph0_iff.mp (lt_of_le_of_lt hrank (Cardinal.natCast_lt_aleph0 (n := n)))
  exact ⟨hfin, Module.finrank_le_of_rank_le hrank⟩


/-! ## Row 468 — existence and uniqueness of the algEquiv over the base change -/

namespace QExpAutBaseChange

variable {K₀ K : Type*} [Field K₀] [Field K] (φ : K₀ →+* K) (Γ : Subgroup SL(2, ℤ))

def Rsub : Subalgebra K (E (K := K) Γ) where
  carrier := Submodule.span K (Set.range (iota φ Γ))
  mul_mem' {a b} ha hb := by
    change a * b ∈ Submodule.span K (Set.range (iota φ Γ))
    refine Submodule.span_induction (p := fun a _ => a * b ∈ Submodule.span K (Set.range (iota φ Γ)))
      ?_ ?_ ?_ ?_ ha
    · rintro _ ⟨y, rfl⟩
      refine Submodule.span_induction (p := fun b _ => iota φ Γ y * b ∈ Submodule.span K (Set.range (iota φ Γ)))
        ?_ ?_ ?_ ?_ hb
      · rintro _ ⟨z, rfl⟩
        rw [← map_mul]
        exact Submodule.subset_span ⟨y * z, rfl⟩
      · show iota φ Γ y * 0 ∈ _
        rw [mul_zero]; exact zero_mem _
      · intro u v _ _ hu hv
        show iota φ Γ y * (u + v) ∈ _
        rw [mul_add]; exact add_mem hu hv
      · intro c u _ hu
        show iota φ Γ y * (c • u) ∈ _
        rw [mul_smul_comm]; exact Submodule.smul_mem _ c hu
    · show (0 : E (K := K) Γ) * b ∈ _
      rw [zero_mul]; exact zero_mem _
    · intro u v _ _ hu hv
      show (u + v) * b ∈ _
      rw [add_mul]; exact add_mem hu hv
    · intro c u _ hu
      show (c • u) * b ∈ _
      rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hu
  add_mem' {a b} ha hb := add_mem ha hb
  algebraMap_mem' c := by
    change algebraMap K (E Γ) c ∈ Submodule.span K (Set.range (iota φ Γ))
    rw [Algebra.algebraMap_eq_smul_one]
    refine Submodule.smul_mem _ c (Submodule.subset_span ⟨1, ?_⟩)
    rw [map_one]

theorem mem_Rsub_iff (a : E (K := K) Γ) :
    a ∈ Rsub φ Γ ↔ a ∈ Submodule.span K (Set.range (iota φ Γ)) := Iff.rfl

theorem iota_mem_Rsub (y : E₀ (K₀ := K₀) Γ) : iota φ Γ y ∈ Rsub φ Γ :=
  Submodule.subset_span ⟨y, rfl⟩

def iotaR (y : E₀ (K₀ := K₀) Γ) : Rsub φ Γ := ⟨iota φ Γ y, iota_mem_Rsub φ Γ y⟩

@[simp] theorem coe_iotaR (y : E₀ (K₀ := K₀) Γ) :
    ((iotaR φ Γ y : Rsub φ Γ) : E (K := K) Γ) = iota φ Γ y := rfl

theorem iotaR_mul (y z : E₀ (K₀ := K₀) Γ) : iotaR φ Γ (y * z) = iotaR φ Γ y * iotaR φ Γ z :=
  Subtype.ext (map_mul _ _ _)

theorem iotaR_one : iotaR φ Γ (1 : E₀ (K₀ := K₀) Γ) = 1 := Subtype.ext (map_one _)

def iotaRsl : E₀ (K₀ := K₀) Γ →ₛₗ[φ] Rsub φ Γ where
  toFun := iotaR φ Γ
  map_add' _a _b := Subtype.ext (map_add _ _ _)
  map_smul' c a := by
    apply Subtype.ext
    rw [Subalgebra.coe_smul, coe_iotaR, coe_iotaR, iota_smul]

@[simp] theorem iotaRsl_apply (y : E₀ (K₀ := K₀) Γ) : iotaRsl φ Γ y = iotaR φ Γ y := rfl

section WithBasis

variable {ιb : Type*} (b : Basis ιb K₀ (E₀ (K₀ := K₀) Γ))

theorem linearIndependent_val_comp {ι : Type*} {v : ι → E₀ (K₀ := K₀) Γ}
    (hv : LinearIndependent K₀ v) :
    LinearIndependent K₀ (fun j => ((v j : E₀ Γ) : LaurentSeries K₀)) :=
  hv.map' (IntermediateField.val _).toLinearMap (LinearMap.ker_eq_bot.mpr Subtype.val_injective)

def w (j : ιb) : Rsub φ Γ := iotaR φ Γ (b j)

def toLaurent : Rsub φ Γ →ₗ[K] LaurentSeries K where
  toFun r := ((r : E (K := K) Γ) : LaurentSeries K)
  map_add' a b := by
    rw [Subalgebra.coe_add, IntermediateField.coe_add]
  map_smul' c a := by
    rw [RingHom.id_apply, Subalgebra.coe_smul, IntermediateField.coe_smul]

theorem toLaurent_apply (r : Rsub φ Γ) :
    toLaurent φ Γ r = ((r : E (K := K) Γ) : LaurentSeries K) := rfl

theorem toLaurent_w (j : ιb) :
    toLaurent φ Γ (w φ Γ b j) = coeffMap φ ((b j : E₀ Γ) : LaurentSeries K₀) := rfl

theorem linearIndependent_w : LinearIndependent K (w φ Γ b) := by
  have h0 : LinearIndependent K₀ (fun j => ((b j : E₀ Γ) : LaurentSeries K₀)) :=
    linearIndependent_val_comp Γ b.linearIndependent
  have h1 := linearIndependent_coeffMap φ h0
  refine LinearIndependent.of_comp (toLaurent φ Γ) ?_
  have hfun : (⇑(toLaurent φ Γ) ∘ w φ Γ b) =
      fun j => coeffMap φ ((b j : E₀ Γ) : LaurentSeries K₀) :=
    funext fun j => toLaurent_w φ Γ b j
  rw [hfun]
  exact h1

def iotaSL : E₀ (K₀ := K₀) Γ →ₛₗ[φ] E (K := K) Γ where
  toFun := iota φ Γ
  map_add' _a _b := map_add _ _ _
  map_smul' c a := iota_smul φ Γ c a

@[simp] theorem iotaSL_apply (y : E₀ (K₀ := K₀) Γ) : iotaSL φ Γ y = iota φ Γ y := rfl

theorem iota_mem_span (y : E₀ (K₀ := K₀) Γ) :
    iota φ Γ y ∈ Submodule.span K (Set.range fun j => iota φ Γ (b j)) := by
  have key : ∀ l : ιb →₀ K₀,
      iotaSL φ Γ (Finsupp.linearCombination K₀ b l) ∈ Submodule.span K (Set.range fun j => iota φ Γ (b j)) := by
    intro l
    rw [Finsupp.linearCombination_apply, map_finsuppSum]
    refine Submodule.finsuppSum_mem _ _ _ _ fun j _ => ?_
    rw [LinearMap.map_smulₛₗ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have := key (b.repr y)
  rwa [b.linearCombination_repr y] at this

theorem range_val_w : Set.range (fun j => ((w φ Γ b j : Rsub φ Γ) : E (K := K) Γ)) =
    Set.range fun j => iota φ Γ (b j) := rfl

theorem span_w : ⊤ ≤ Submodule.span K (Set.range (w φ Γ b)) := by
  intro r _
  have h1 : (r : E (K := K) Γ) ∈ Submodule.span K (Set.range (iota φ Γ)) := r.2
  have h2 : Submodule.span K (Set.range (iota φ Γ)) ≤
      Submodule.span K (Set.range fun j => iota φ Γ (b j)) :=
    Submodule.span_le.mpr (by
      rintro _ ⟨y, rfl⟩
      exact iota_mem_span φ Γ b y)
  have h3 : Submodule.span K (Set.range fun j => iota φ Γ (b j)) =
      (Submodule.span K (Set.range (w φ Γ b))).map (Rsub φ Γ).val.toLinearMap := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  have h4 := h2 h1
  rw [h3, Submodule.mem_map] at h4
  obtain ⟨r', hr', hval⟩ := h4
  have : r' = r := Subtype.ext hval
  rw [← this]
  exact hr'

def bR : Basis ιb K (Rsub φ Γ) :=
  Basis.mk (linearIndependent_w φ Γ b) (span_w φ Γ b)

theorem bR_apply (j : ιb) : bR φ Γ b j = iotaR φ Γ (b j) :=
  Basis.mk_apply _ _ j

section Sigma

variable (σ₀ : E₀ (K₀ := K₀) Γ ≃ₐ[K₀] E₀ (K₀ := K₀) Γ)

def sigmaR : Rsub φ Γ →ₗ[K] Rsub φ Γ :=
  (bR φ Γ b).constr K fun j => iotaR φ Γ (σ₀ (b j))

theorem sigmaR_bR (j : ιb) :
    sigmaR φ Γ b σ₀ (bR φ Γ b j) = iotaR φ Γ (σ₀ (b j)) :=
  Basis.constr_basis _ _ _ j

theorem sigmaR_iotaR (y : E₀ (K₀ := K₀) Γ) :
    sigmaR φ Γ b σ₀ (iotaR φ Γ y) = iotaR φ Γ (σ₀ y) := by
  have key : (sigmaR φ Γ b σ₀).comp (iotaRsl φ Γ) = (iotaRsl φ Γ).comp σ₀.toLinearMap := by
    refine b.ext fun j => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, iotaRsl_apply, ← bR_apply, sigmaR_bR]
    rfl
  have := congrArg (fun f => f y) key
  simpa using this

theorem sigmaR_one : sigmaR φ Γ b σ₀ 1 = 1 := by
  rw [← iotaR_one, sigmaR_iotaR, map_one, iotaR_one]

theorem sigmaR_mul (r s : Rsub φ Γ) :
    sigmaR φ Γ b σ₀ (r * s) = sigmaR φ Γ b σ₀ r * sigmaR φ Γ b σ₀ s := by
  have key : (LinearMap.mul K (Rsub φ Γ)).compr₂ (sigmaR φ Γ b σ₀) =
      (LinearMap.mul K (Rsub φ Γ)).compl₁₂ (sigmaR φ Γ b σ₀) (sigmaR φ Γ b σ₀) := by
    refine (bR φ Γ b).ext fun i => (bR φ Γ b).ext fun j => ?_
    simp only [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, LinearMap.mul_apply']
    rw [bR_apply, bR_apply, ← iotaR_mul, sigmaR_iotaR, sigmaR_iotaR, sigmaR_iotaR, map_mul, iotaR_mul]
  have := congrArg (fun f => f r s) key
  simpa using this

theorem sigmaR_symm_sigmaR (r : Rsub φ Γ) :
    sigmaR φ Γ b σ₀.symm (sigmaR φ Γ b σ₀ r) = r := by
  have key : (sigmaR φ Γ b σ₀.symm).comp (sigmaR φ Γ b σ₀) = LinearMap.id := by
    refine (bR φ Γ b).ext fun j => ?_
    rw [LinearMap.comp_apply, LinearMap.id_apply, bR_apply, sigmaR_iotaR, sigmaR_iotaR,
      AlgEquiv.symm_apply_apply]
  exact congrArg (fun f => f r) key

def sigmaRequiv : Rsub φ Γ ≃ₗ[K] Rsub φ Γ :=
  LinearEquiv.ofBijective (sigmaR φ Γ b σ₀)
    ⟨fun r s hrs => by
      have h := congrArg (sigmaR φ Γ b σ₀.symm) hrs
      simpa only [sigmaR_symm_sigmaR] using h,
    fun r => ⟨sigmaR φ Γ b σ₀.symm r, sigmaR_symm_sigmaR φ Γ b σ₀.symm r⟩⟩

def eR : Rsub φ Γ ≃ₐ[K] Rsub φ Γ :=
  AlgEquiv.ofLinearEquiv (sigmaRequiv φ Γ b σ₀) (sigmaR_one φ Γ b σ₀) (sigmaR_mul φ Γ b σ₀)

theorem eR_apply (r : Rsub φ Γ) : eR φ Γ b σ₀ r = sigmaR φ Γ b σ₀ r := rfl

theorem eR_iotaR (y : E₀ (K₀ := K₀) Γ) : eR φ Γ b σ₀ (iotaR φ Γ y) = iotaR φ Γ (σ₀ y) :=
  sigmaR_iotaR φ Γ b σ₀ y

end Sigma

theorem exists_Rsub_of_mem_closure {t : LaurentSeries K}
    (ht : t ∈ Subring.closure (Set.range (algebraMap K (LaurentSeries K)) ∪ intFormRatiosC K Γ)) :
    ∃ r : Rsub φ Γ, ((r : E (K := K) Γ) : LaurentSeries K) = t := by
  let Rimg : Subring (LaurentSeries K) :=
    (Rsub φ Γ).toSubring.map ((IntermediateField.val (qExpFunctionFieldC K Γ)) : E Γ →+* LaurentSeries K)
  have hle : Subring.closure (Set.range (algebraMap K (LaurentSeries K)) ∪ intFormRatiosC K Γ) ≤ Rimg := by
    refine Subring.closure_le.mpr ?_
    rintro y (⟨c, rfl⟩ | hy)
    · exact ⟨algebraMap K (E Γ) c, (Rsub φ Γ).algebraMap_mem c, rfl⟩
    · rw [intFormRatiosC_eq_image φ Γ] at hy
      obtain ⟨y₀, hy₀, rfl⟩ := hy
      exact ⟨iota φ Γ ⟨y₀, intFormRatiosC_subset K₀ Γ hy₀⟩, iota_mem_Rsub φ Γ _, rfl⟩
  obtain ⟨r, hr, hrt⟩ := hle ht
  exact ⟨⟨r, hr⟩, hrt⟩

scoped instance isFractionRing_Rsub : IsFractionRing (Rsub φ Γ) (E (K := K) Γ) where
  map_units := by
    rintro ⟨s, hs⟩
    have hs0 : (s : E (K := K) Γ) ≠ 0 := fun h =>
      nonZeroDivisors.ne_zero hs (Subtype.ext (by rw [h]; rfl))
    exact isUnit_iff_ne_zero.mpr hs0
  surj := by
    intro z
    have hz : (z : LaurentSeries K) ∈ (IntermediateField.adjoin K (intFormRatiosC K Γ)).toSubfield := z.2
    rw [IntermediateField.adjoin_toSubfield, Subfield.mem_closure_iff] at hz
    obtain ⟨y, hy, y', hy', hyz⟩ := hz
    obtain ⟨a, ha⟩ := exists_Rsub_of_mem_closure φ Γ hy
    obtain ⟨s, hs⟩ := exists_Rsub_of_mem_closure φ Γ hy'
    rw [← ha, ← hs] at hyz
    by_cases hs0 : ((s : E (K := K) Γ) : LaurentSeries K) = 0
    · refine ⟨(0, 1), ?_⟩
      have hz0 : z = 0 := by
        apply Subtype.ext
        rw [← hyz, hs0, div_zero]
        rfl
      rw [hz0]
      simp
    · have hsE : (s : E (K := K) Γ) ≠ 0 := fun h => hs0 (by rw [h]; rfl)
      have hsR : s ≠ 0 := fun h => hsE (by rw [h]; rfl)
      refine ⟨(a, ⟨s, mem_nonZeroDivisors_of_ne_zero hsR⟩), ?_⟩
      show z * (s : E (K := K) Γ) = (a : E (K := K) Γ)
      apply Subtype.ext
      rw [MulMemClass.coe_mul, ← hyz, div_mul_cancel₀ _ hs0]
  exists_of_eq := by
    intro x y h
    have hxy : x = y := Subtype.ext h
    exact ⟨1, by rw [hxy]⟩

section Sigma

variable (σ₀ : E₀ (K₀ := K₀) Γ ≃ₐ[K₀] E₀ (K₀ := K₀) Γ)

def sigmaE : E (K := K) Γ ≃+* E (K := K) Γ :=
  IsFractionRing.ringEquivOfRingEquiv (eR φ Γ b σ₀ : Rsub φ Γ ≃+* Rsub φ Γ)

theorem sigmaE_coe (r : Rsub φ Γ) :
    sigmaE φ Γ b σ₀ (r : E (K := K) Γ) = (eR φ Γ b σ₀ r : Rsub φ Γ) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap (eR φ Γ b σ₀ : Rsub φ Γ ≃+* Rsub φ Γ) r

theorem eR_ringEquiv_apply (r : Rsub φ Γ) :
    (eR φ Γ b σ₀ : Rsub φ Γ ≃+* Rsub φ Γ) r = eR φ Γ b σ₀ r := rfl

theorem sigmaE_algebraMap (c : K) : sigmaE φ Γ b σ₀ (algebraMap K (E Γ) c) = algebraMap K (E Γ) c := by
  rw [IsScalarTower.algebraMap_apply K (Rsub φ Γ) (E Γ) c, sigmaE,
    IsFractionRing.ringEquivOfRingEquiv_algebraMap, eR_ringEquiv_apply, AlgEquiv.commutes]

def sigma : E (K := K) Γ ≃ₐ[K] E (K := K) Γ :=
  AlgEquiv.ofRingEquiv (f := sigmaE φ Γ b σ₀) (sigmaE_algebraMap φ Γ b σ₀)

theorem sigma_iota (y : E₀ (K₀ := K₀) Γ) : sigma φ Γ b σ₀ (iota φ Γ y) = iota φ Γ (σ₀ y) := by
  change sigmaE φ Γ b σ₀ ((iotaR φ Γ y : Rsub φ Γ) : E (K := K) Γ) = _
  rw [sigmaE_coe, eR_iotaR]
  rfl

end Sigma

theorem algEquiv_eq_of_iota (τ τ' : E (K := K) Γ ≃ₐ[K] E (K := K) Γ)
    (h : ∀ y : E₀ (K₀ := K₀) Γ, τ (iota φ Γ y) = τ' (iota φ Γ y)) : τ = τ' := by
  let Q : IntermediateField K (E (K := K) Γ) :=
    { carrier := {z | τ z = τ' z}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq, map_mul] at *; rw [ha, hb]
      one_mem' := by simp
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq, map_add] at *; rw [ha, hb]
      zero_mem' := by simp
      algebraMap_mem' := fun c => by
        simp only [Set.mem_ofPred_eq, AlgEquiv.commutes]
      inv_mem' := fun x hx => by
        simp only [Set.mem_ofPred_eq, map_inv₀] at *; rw [hx] }
  have hgen : qExpFunctionFieldC K Γ ≤ IntermediateField.lift Q := by
    conv_lhs => rw [qExpFunctionFieldC]
    rw [adjoin_le_iff]
    intro s hs
    have hs' := hs
    rw [intFormRatiosC_eq_image φ Γ] at hs'
    obtain ⟨s₀, hs₀, rfl⟩ := hs'
    have hmem : (⟨_, intFormRatiosC_subset K Γ hs⟩ : E (K := K) Γ) ∈ Q := by
      change τ _ = τ' _
      have : (⟨_, intFormRatiosC_subset K Γ hs⟩ : E (K := K) Γ) =
          iota φ Γ ⟨s₀, intFormRatiosC_subset K₀ Γ hs₀⟩ :=
        Subtype.ext rfl
      rw [this]
      exact h _
    exact (mem_lift (⟨_, intFormRatiosC_subset K Γ hs⟩ : E (K := K) Γ)).mpr hmem
  refine AlgEquiv.ext fun z => ?_
  have hz : (z : LaurentSeries K) ∈ IntermediateField.lift Q := hgen z.2
  exact (mem_lift z).mp hz

end WithBasis

end QExpAutBaseChange

theorem existsUnique_algEquiv_qExpFunctionFieldC_coe_apply_eq_coeffMap
    {K₀ K : Type*} [Field K₀] [Field K] (φ : K₀ →+* K)
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
    (σ₀ : qExpFunctionFieldC K₀ Γ ≃ₐ[K₀] qExpFunctionFieldC K₀ Γ) :
    ∃! σ : qExpFunctionFieldC K Γ ≃ₐ[K] qExpFunctionFieldC K Γ,
      ∀ (x₀ : qExpFunctionFieldC K₀ Γ) (x : qExpFunctionFieldC K Γ),
        (x : LaurentSeries K) = coeffMap φ (x₀ : LaurentSeries K₀) →
        ((σ x : qExpFunctionFieldC K Γ) : LaurentSeries K) =
          coeffMap φ ((σ₀ x₀ : qExpFunctionFieldC K₀ Γ) : LaurentSeries K₀) := by
  refine ⟨QExpAutBaseChange.sigma φ Γ (Module.Basis.ofVectorSpace K₀ _) σ₀, ?_, ?_⟩
  · intro x₀ x hx
    have : x = QExpAutBaseChange.iota φ Γ x₀ := Subtype.ext hx
    rw [this, QExpAutBaseChange.sigma_iota]
    rfl
  · intro τ hτ
    refine QExpAutBaseChange.algEquiv_eq_of_iota φ Γ τ _ fun y => ?_
    apply Subtype.ext
    rw [hτ y _ rfl, QExpAutBaseChange.sigma_iota]
    rfl


end ModularCurve
