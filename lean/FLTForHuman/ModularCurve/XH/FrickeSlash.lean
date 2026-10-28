/-
  The Fricke slash of a `Γ_H(M)`-form with rational `q`-expansion, as a finite `ℚ̄`-sum.

  `ModularCurve.exists_slash_fricke_eq_sum_smul_of_ratCast_qExpansion`: for a weight-`k`
  form `f` on `Γ_H(M) = CohCarrier.GammaH M H` whose level-one `q`-expansion has rational
  coefficients, and for any `W ∈ GL(2, ℝ)` whose matrix is the Fricke matrix
  `!![0, -1; M, 0]`, the slash `f ∣[k] W` is a finite `ℚ̄`-linear combination
  `∑ i, ι (c i) • g i` of forms `g i` on `Γ_H(M)`, each of which admits an integral
  `q`-expansion `p i` (`ModularCurve.IsIntegralQExp (g i) (p i)`), for the coefficient
  embedding `ι : ℚ̄ →+* ℂ`.

  The route is the pin's, in four steps.

  * **The Fricke translate.** `frickeGL M = !![0, -1; M, 0]` as an element of
    `GL(2, ℝ)`, and `frickeForm f = restrictForm le_conj_frickeGL (translate f (frickeGL M))`:
    the conjugate `F Γ_H(M) F⁻¹` is `Γ_H(M)` again (`frickeGL_mul_mul_inv`, through the
    Fricke involution `CohCarrier.frickeMat` of the matrix group), so the translate is a
    form on `Γ_H(M)`.
  * **The reciprocity.** `exists_qExpansion_slash_fricke_eq_and_conj_eq_slash_gamma0` gives
    the `q`-expansion of `f ∣[k] frickeGL M` as `ι` of an integral model
    `a : ℕ → ℚ̄`, together with the Galois law `σ (a n) = a n` twisted by the `Γ₀(M)`-slash
    whose lower-right entry reduces to the cyclotomic exponent of `σ`.
  * **The descent.** The fixed field `K` of the cyclotomic twist
    (`exists_intermediateField_of_fixed`, over `∃ ζ, IsPrimitiveRoot ζ M`) contains every
    coefficient of the model, and the twists realize the whole Galois action on it, so the
    `PowerSeries` descent `exists_map_eq_sum_smul_map_of_forall_map_algEquiv_mem` writes
    `A.map ι` as `∑ i, ι (c i) • r i` with `r i` over `ℚ` and every `r i` in the range of
    the `q`-expansion map `qExpL` on `Γ_H(M)`-forms.
  * **The integrality.** `exists_isIntegralQExp_smul_of_ratCast_qExpansion` clears the
    denominators of each `r i` to an integral `q`-expansion `p i` of `(D i : ℂ) • R i`, and
    `ι (c i / D i)` is the coefficient of that form.

  The pin declares this engine (`frickeGL`, `frickeForm`, the cyclotomic block, the
  `q`-expansion submodule `qExpSubmodule` and its linear map `qExpL`) inside its `S_` file;
  it is transcribed here, `private`, so the module's public surface is exactly the headline.
  `frickeGL` takes its body from the port's promoted `ALTraceIdentity.frickeGL` at the pin's
  `[NeZero M]` binder spelling (`HeckeFrickeTrace.lean`), and `ΓGL` is the port's
  `ModularForm.Level.ΓGL` — the same abbreviation the pin carries in this prelude. Three
  private adapters (`mapGL_coe`, `mapGL_mul'`, `mapGL_inv'`) spell `mapGL ℝ` as a matrix, a
  product and an inverse so that the matrix-entry computation of `frickeGL_mul_mul_inv` and
  the `SL(2, ℤ) → GL(2, ℝ)` coercion of `le_conj_gamma0` can be rewritten in mathlib
  `v4.34.0`'s coercion spelling. The pin's `attribute [-simp]` prelude is not transcribed
  (the port keeps those lemmas global), nor is its `p2m_export` / `p2m_open` scaffolding.

  Transcribed from the pin's `P2M/Sol/S_ModularCurve_exists_slash_fricke_eq_sum_smul_of_ratCast_qExpansion.lean`
  (322 lines), statements at the pin's `Theorems/` wrapper. The pin's `scoped` instances
  `isAlgebraicQbar`/`isAlgClosureQbar`/`isGaloisQbar` are not transcribed: mathlib `v4.34.0`
  already has `AlgebraicClosure.isAlgebraic`, the `IsAlgClosure` instance of
  `AlgebraicClosure` and hence `IsAlgClosure.isGalois`'s `IsGalois` instance for it.

  FLT provenance, pinned `aa2d8b3`:
  <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_exists_slash_fricke_eq_sum_smul_of_ratCast_qExpansion.lean>,
  <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_exists_slash_fricke_eq_sum_smul_of_ratCast_qExpansion.lean>
  spec-pin: Theorems/Thm_ModularCurve_exists_slash_fricke_eq_sum_smul_of_ratCast_qExpansion.lean
  spec-pin: P2M/Sol/S_ModularCurve_exists_slash_fricke_eq_sum_smul_of_ratCast_qExpansion.lean
-/
import FLTForHuman.ModularCurve.X1.Defs
import FLTForHuman.ModularForms.CohCarrier.Fricke
import FLTForHuman.ModularForms.FrickeReciprocity
import FLTForHuman.ModularForms.WeightOne.Gamma0Integral
import FLTForHuman.RingTheory.PowerSeries.GaloisDescent
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section

open UpperHalfPlane CongruenceSubgroup Matrix IntermediateField
open scoped MatrixGroups ModularForm Pointwise

open ModularForm.Level (ΓGL)

namespace ModularCurve

/-! ## The Fricke translate on `Γ_H(M)` -/

section Groups

variable {M : ℕ} {H : Subgroup (ZMod M)ˣ}

/-- A subgroup of `SL(2, ℤ)` containing the translation `T` has `1` among its strict periods:
its strict periods are `ℤ` (`Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem`). -/
private theorem one_mem_strictPeriods_of_T_mem {Γ : Subgroup SL(2, ℤ)} (hT : ModularGroup.T ∈ Γ) :
    (1 : ℝ) ∈ (ΓGL Γ).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem hT]
  exact AddSubgroup.mem_zmultiples _

/-- The Fricke matrix `!![0, -1; M, 0]` as an element of `GL(2, ℝ)`. -/
private def frickeGL (M : ℕ) [NeZero M] : GL (Fin 2) ℝ :=
  ALTraceIdentity.frickeGL M (NeZero.ne M)

@[scoped simp] private theorem val_frickeGL [NeZero M] :
    ((frickeGL M : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; (M : ℝ), 0] := rfl

private theorem det_frickeGL [NeZero M] : ((frickeGL M).det : ℝ) = M := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, val_frickeGL, Matrix.det_fin_two_of]; ring

private theorem det_frickeGL_pos [NeZero M] : 0 < ((frickeGL M).det : ℝ) := by
  rw [det_frickeGL]; exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)

/-- The Fricke matrix is the only `GL(2, ℝ)`-element whose matrix is `!![0, -1; M, 0]`. -/
private theorem eq_frickeGL [NeZero M] {W : GL (Fin 2) ℝ}
    (hW : (W : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; (M : ℝ), 0]) : W = frickeGL M :=
  Units.ext (by rw [hW]; rfl)

private theorem mapGL_eq_coe (γ : SL(2, ℤ)) :
    Matrix.SpecialLinearGroup.mapGL ℝ γ = (γ : GL (Fin 2) ℝ) := rfl

/-- The matrix of `mapGL ℝ γ`: the `ℤ`-matrix of `γ` with its entries cast to `ℝ`. -/
private theorem mapGL_coe (γ : SL(2, ℤ)) :
    ((Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      = (↑γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℝ) := rfl

/-- The Fricke matrix conjugates `Γ₀(M)` into `SL(2, ℤ)`: `F γ F⁻¹` is the Fricke transform
`CohCarrier.frickeMat` of `γ`, for a `γ` whose lower-left entry is divisible by `M`. -/
private theorem frickeGL_mul_mul_inv [NeZero M] (γ : SL(2, ℤ)) (h : (M : ℤ) ∣ γ 1 0) :
    frickeGL M * Matrix.SpecialLinearGroup.mapGL ℝ γ * (frickeGL M)⁻¹ =
      Matrix.SpecialLinearGroup.mapGL ℝ (CohCarrier.frickeMat M γ h) := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Units.ext
  simp only [GeneralLinearGroup.coe_mul, val_frickeGL, mapGL_coe]
  obtain ⟨c, hc⟩ := h
  have hc' : (M * c / M : ℤ) = c := by
    rw [Int.mul_ediv_cancel_left _ (by exact_mod_cast NeZero.ne M)]
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply, Int.coe_castRingHom,
      CohCarrier.frickeMat_apply_00, CohCarrier.frickeMat_apply_01,
      CohCarrier.frickeMat_apply_10, CohCarrier.frickeMat_apply_11, hc] <;> ring)

/-- `Γ_H(M)` is stable under conjugation by the Fricke matrix, so the Fricke translate of a
`Γ_H(M)`-form restricts back to a `Γ_H(M)`-form. -/
private theorem le_conj_frickeGL [NeZero M] :
    ΓGL (CohCarrier.GammaH M H) ≤
      ConjAct.toConjAct (frickeGL M)⁻¹ • ΓGL (CohCarrier.GammaH M H) := by
  rintro x ⟨δ, hδ, rfl⟩
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, inv_inv,
    ConjAct.toConjAct_smul]
  have h10 := CohCarrier.N_dvd_of_mem_GammaH M H ⟨δ, hδ⟩
  exact ⟨CohCarrier.frickeMat M δ h10, CohCarrier.frickeMat_mem M H ⟨δ, hδ⟩,
    (frickeGL_mul_mul_inv δ h10).symm⟩

/-- The Fricke translate `f ∣[k] !![0, -1; M, 0]` of a `Γ_H(M)`-form, as a form on
`Γ_H(M)`. -/
private def frickeForm [NeZero M] {k : ℤ} (f : ModularForm (ΓGL (CohCarrier.GammaH M H)) k) :
    ModularForm (ΓGL (CohCarrier.GammaH M H)) k :=
  restrictForm le_conj_frickeGL (ModularForm.translate f (frickeGL M))

@[scoped simp] private theorem coe_frickeForm [NeZero M] {k : ℤ}
    (f : ModularForm (ΓGL (CohCarrier.GammaH M H)) k) :
    ⇑(frickeForm f) = ⇑f ∣[k] frickeGL M := rfl

omit H in
/-- The scalar action on `Γ_H(M)`-forms is pointwise on the underlying function. -/
private theorem coe_smul_form {Γ : Subgroup SL(2, ℤ)} {k : ℤ} (c : ℂ)
    (f : ModularForm (ΓGL Γ) k) : ⇑(c • f) = c • ⇑f := rfl

/-- `mapGL` is a monoid homomorphism, read at a product. -/
private theorem mapGL_mul' (γ δ : SL(2, ℤ)) :
    Matrix.SpecialLinearGroup.mapGL ℝ (γ * δ) =
      Matrix.SpecialLinearGroup.mapGL ℝ γ * Matrix.SpecialLinearGroup.mapGL ℝ δ :=
  map_mul _ γ δ

private theorem mapGL_inv' (γ : SL(2, ℤ)) :
    Matrix.SpecialLinearGroup.mapGL ℝ γ⁻¹ = (Matrix.SpecialLinearGroup.mapGL ℝ γ)⁻¹ :=
  map_inv _ γ

/-- A `Γ₀(M)`-matrix normalizes `Γ_H(M)`: the conjugate of `δ ∈ Γ_H(M)` by `γ ∈ Γ₀(M)` is
again in `Γ_H(M)` and has the same lower-right unit. -/
private theorem le_conj_gamma0 {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) :
    ΓGL (CohCarrier.GammaH M H) ≤
      ConjAct.toConjAct ((γ : GL (Fin 2) ℝ))⁻¹ • ΓGL (CohCarrier.GammaH M H) := by
  rintro x ⟨δ, hδ, rfl⟩
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, inv_inv,
    ConjAct.toConjAct_smul]
  refine ⟨γ * δ * γ⁻¹, CohCarrier.conj_mem_GammaH M H ⟨γ, hγ⟩ ⟨δ, hδ⟩, ?_⟩
  rw [mapGL_mul', mapGL_mul', mapGL_inv']
  rfl

/-- The slash of a `Γ_H(M)`-form by a `Γ₀(M)`-matrix, as a form on `Γ_H(M)`. -/
private def slashForm {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M)
    (f : ModularForm (ΓGL (CohCarrier.GammaH M H)) k) :
    ModularForm (ΓGL (CohCarrier.GammaH M H)) k :=
  restrictForm (le_conj_gamma0 hγ) (ModularForm.translate f (γ : GL (Fin 2) ℝ))

@[scoped simp] private theorem coe_slashForm {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M)
    (f : ModularForm (ΓGL (CohCarrier.GammaH M H)) k) :
    ⇑(slashForm γ hγ f) = ⇑f ∣[k] (γ : GL (Fin 2) ℝ) := rfl

end Groups

/-! ## The cyclotomic twist of `ℚ̄` -/

section Cyclo

local notation "Qb" => AlgebraicClosure ℚ

variable (M : ℕ) [NeZero M]

/-- `ℚ̄` contains a primitive `M`-th root of unity. -/
private theorem exists_isPrimitiveRoot : ∃ ζ : Qb, IsPrimitiveRoot ζ M := by
  have hdeg : (Polynomial.cyclotomic M Qb).degree ≠ 0 := by
    rw [Polynomial.degree_cyclotomic]
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne M))).ne'
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root _ hdeg
  exact ⟨ζ, Polynomial.isRoot_cyclotomic_iff.mp hζ⟩

variable {M}

omit [NeZero M] in
/-- Exponents of an `M`-th root of unity reduce modulo `M`. -/
private theorem pow_eq_pow_mod {ζ : Qb} (hζ : ζ ^ M = 1) (n : ℕ) : ζ ^ n = ζ ^ (n % M) := by
  conv_lhs => rw [← Nat.div_add_mod n M, _root_.pow_add, _root_.pow_mul, hζ, one_pow, one_mul]

variable (M) in
/-- A `ℚ`-automorphism of `ℚ̄` acts on the `M`-th roots of unity by a power `c` coprime to
`M`. -/
private theorem exists_coprime_forall_pow (σ : Qb ≃ₐ[ℚ] Qb) :
    ∃ c : ℕ, c.Coprime M ∧ ∀ ζ : Qb, ζ ^ M = 1 → σ ζ = ζ ^ c := by
  obtain ⟨ζ₀, h0⟩ := exists_isPrimitiveRoot M
  have h1 : (σ ζ₀) ^ M = 1 := by rw [← map_pow, h0.pow_eq_one, map_one]
  obtain ⟨c, -, hc⟩ := h0.eq_pow_of_pow_eq_one h1
  have hprim : IsPrimitiveRoot (σ ζ₀) M := h0.map_of_injective σ.injective
  rw [← hc] at hprim
  have hcop : c.Coprime M := (h0.pow_iff_coprime (Nat.pos_of_ne_zero (NeZero.ne M)) c).mp hprim
  refine ⟨c, hcop, fun ζ hζ => ?_⟩
  obtain ⟨j, -, rfl⟩ := h0.eq_pow_of_pow_eq_one hζ
  rw [map_pow, ← hc, ← pow_mul, ← pow_mul, mul_comm]

variable (M) in
/-- The fixed field of the cyclotomic twist: some finite extension of `ℚ` inside `ℚ̄`
contains every element fixed by all the automorphisms that fix the `M`-th roots of
unity. -/
private theorem exists_intermediateField_of_fixed :
    ∃ K : IntermediateField ℚ Qb, FiniteDimensional ℚ K ∧
      ∀ x : Qb, (∀ σ : Qb ≃ₐ[ℚ] Qb, (∀ ζ : Qb, ζ ^ M = 1 → σ ζ = ζ) → σ x = x) → x ∈ K := by
  obtain ⟨ζ₀, h0⟩ := exists_isPrimitiveRoot M
  refine ⟨IntermediateField.adjoin ℚ {ζ₀},
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral ζ₀), fun x hx => ?_⟩
  rw [← InfiniteGalois.fixedField_fixingSubgroup (IntermediateField.adjoin ℚ {ζ₀}),
    IntermediateField.mem_fixedField_iff]
  intro σ hσ
  apply hx σ
  intro ζ hζ
  have hfix : σ ζ₀ = ζ₀ := by
    rw [IntermediateField.mem_fixingSubgroup_iff] at hσ
    exact hσ ζ₀ (IntermediateField.mem_adjoin_simple_self ℚ ζ₀)
  obtain ⟨j, -, rfl⟩ := h0.eq_pow_of_pow_eq_one hζ
  rw [map_pow, hfix]

end Cyclo

/-! ## The `q`-expansion of `Γ_H(M)`-forms as a submodule -/

section Span

local notation "Qb" => AlgebraicClosure ℚ

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ}

/-- A `Γ_H(M)`-form as a `Γ₁(M)`-form, by restriction along `Γ₁(M) ≤ Γ_H(M)`. -/
private def res1 {k : ℤ} (f : ModularForm (ΓGL (CohCarrier.GammaH M H)) k) :
    ModularForm (Gamma1 M : Subgroup (GL (Fin 2) ℝ)) k :=
  restrictForm (Subgroup.map_mono (CohCarrier.Gamma1_le_GammaH M H)) f

omit [NeZero M] in
@[scoped simp] private theorem coe_res1 {k : ℤ} (f : ModularForm (ΓGL (CohCarrier.GammaH M H)) k) :
    ⇑(res1 f) = ⇑f := rfl

/-- The `q`-expansion of `Γ_H(M)`-forms is a `ℂ`-submodule of `ℂ⟦q⟧`. -/
private def qExpSubmodule (M : ℕ) (H : Subgroup (ZMod M)ˣ) (k : ℤ) :
    Submodule ℂ (PowerSeries ℂ) where
  carrier := {P | ∃ f : ModularForm (ΓGL (CohCarrier.GammaH M H)) k, qExpansion 1 ⇑f = P}
  add_mem' := by
    rintro _ _ ⟨f, rfl⟩ ⟨g, rfl⟩
    refine ⟨f + g, ?_⟩
    exact ModularForm.qExpansion_add one_pos
      (one_mem_strictPeriods_of_T_mem (CohCarrier.translation_mem_GammaH M H)) f g
  zero_mem' := ⟨0, by rw [FunLike.coe_zero]; exact qExpansion_zero 1⟩
  smul_mem' := by
    rintro c _ ⟨f, rfl⟩
    refine ⟨c • f, ?_⟩
    exact ModularForm.qExpansion_smul one_pos
      (one_mem_strictPeriods_of_T_mem (CohCarrier.translation_mem_GammaH M H)) c f

omit [NeZero M] in
private theorem mem_qExpSubmodule_iff {k : ℤ} {P : PowerSeries ℂ} :
    P ∈ qExpSubmodule M H k ↔
      ∃ f : ModularForm (ΓGL (CohCarrier.GammaH M H)) k, qExpansion 1 ⇑f = P :=
  Iff.rfl

/-- Every unit of `ZMod M` is the lower-right entry of a `Γ₀(M)`-matrix. -/
private theorem exists_gamma0_lowerRight (d : (ZMod M)ˣ) :
    ∃ γ : SL(2, ℤ), ∃ _ : γ ∈ Gamma0 M, ((γ 1 1 : ℤ) : ZMod M) = d := by
  obtain ⟨γd, hγd⟩ := CohCarrier.gamma0Units_surjective M d
  refine ⟨γd, γd.2, ?_⟩
  have := congrArg (fun u : (ZMod M)ˣ => (u : ZMod M)) hγd
  simpa [CohCarrier.gamma0Units, Gamma0Map] using this

/-- The `q`-expansion of `Γ_H(M)`-forms, as a `ℂ`-linear map. -/
private def qExpL (M : ℕ) (H : Subgroup (ZMod M)ˣ) (k : ℤ) :
    ModularForm (ΓGL (CohCarrier.GammaH M H)) k →ₗ[ℂ] PowerSeries ℂ where
  toFun f := qExpansion 1 ⇑f
  map_add' f g :=
    ModularForm.qExpansion_add one_pos
      (one_mem_strictPeriods_of_T_mem (CohCarrier.translation_mem_GammaH M H)) f g
  map_smul' c f := by
    rw [RingHom.id_apply]
    exact ModularForm.qExpansion_smul one_pos
      (one_mem_strictPeriods_of_T_mem (CohCarrier.translation_mem_GammaH M H)) c f

omit [NeZero M] in
private theorem qExpL_apply {k : ℤ} (f : ModularForm (ΓGL (CohCarrier.GammaH M H)) k) :
    qExpL M H k f = qExpansion 1 ⇑f := rfl

omit [NeZero M] in
/-- The `q`-expansion map of `Γ_H(M)`-forms is injective: a form whose `q`-expansion
vanishes is zero. -/
private theorem qExpL_injective {k : ℤ} : Function.Injective (qExpL M H k) := by
  intro f g h
  have h0 : qExpL M H k (f - g) = 0 := by rw [map_sub, h, sub_self]
  rw [qExpL_apply] at h0
  exact sub_eq_zero.mp ((ModularForm.qExpansion_eq_zero_iff one_pos
    (one_mem_strictPeriods_of_T_mem (CohCarrier.translation_mem_GammaH M H)) (f - g)).mp h0)

variable (ι : Qb →+* ℂ)

/-- **The Fricke slash as a `ℚ̄`-sum.** For a `Γ_H(M)`-form `f` with rational `q`-expansion,
`f ∣[k] frickeGL M` is a finite `ℚ̄`-linear combination of `Γ_H(M)`-forms each of which has
an integral `q`-expansion. -/
private theorem exists_slash_frickeGL_eq_sum {k : ℤ}
    (f : ModularForm (ΓGL (CohCarrier.GammaH M H)) k)
    (hfrat : ∀ n : ℕ, ∃ r : ℚ, (qExpansion 1 ⇑f).coeff n = (r : ℂ)) :
    ∃ (n : ℕ) (c : Fin n → Qb) (g : Fin n → ModularForm (ΓGL (CohCarrier.GammaH M H)) k)
      (p : Fin n → PowerSeries ℤ), (∀ i, IsIntegralQExp (g i) (p i)) ∧
        (⇑f : UpperHalfPlane → ℂ) ∣[k] frickeGL M =
          ∑ i, ι (c i) • (⇑(g i) : UpperHalfPlane → ℂ) := by
  obtain ⟨a, ha1, ha2⟩ :=
    ModularCurve.exists_qExpansion_slash_fricke_eq_and_conj_eq_slash_gamma0 M (res1 f) hfrat ι
      (frickeGL M) val_frickeGL
  simp only [coe_res1] at ha1 ha2
  set A : PowerSeries Qb := PowerSeries.mk a with hA
  have hAmap : A.map ι = qExpansion 1 (⇑f ∣[k] frickeGL M) := by
    ext n; rw [PowerSeries.coeff_map, hA, PowerSeries.coeff_mk, ha1]

  obtain ⟨K, hKfin, hKmem⟩ := exists_intermediateField_of_fixed M
  have hAK : ∀ n, PowerSeries.coeff n A ∈ K := by
    intro n
    rw [hA, PowerSeries.coeff_mk]
    refine hKmem (a n) fun σ hσ => ι.injective ?_
    have h1 : (1 : SL(2, ℤ)) ∈ Gamma0 M := one_mem _
    have h11 : (((1 : SL(2, ℤ)) 1 1 : ℤ) : ZMod M) = ((1 : ℕ) : ZMod M) := by simp
    have h2 := ha2 σ 1 (fun ζ hζ => by rw [pow_one]; exact hσ ζ hζ) 1 h1 h11 n
    rw [← h2, ← ha1 n]
    have e : ((1 : SL(2, ℤ)) : GL (Fin 2) ℝ) = 1 := map_one (Matrix.SpecialLinearGroup.mapGL ℝ)
    rw [e, SlashAction.slash_one]

  have hV : ∀ σ : Qb ≃ₐ[ℚ] Qb, A.map (ι.comp (σ : Qb →+* Qb)) ∈ LinearMap.range (qExpL M H k) := by
    intro σ
    obtain ⟨c, hcop, hσ⟩ := exists_coprime_forall_pow M σ
    obtain ⟨γ, hγ, hγc⟩ := exists_gamma0_lowerRight (M := M) (ZMod.unitOfCoprime c hcop)
    rw [ZMod.coe_unitOfCoprime] at hγc
    refine ⟨slashForm γ hγ (frickeForm f), ?_⟩
    ext n
    rw [qExpL_apply, coe_slashForm, coe_frickeForm, ha2 σ c hσ γ hγ hγc n, PowerSeries.coeff_map,
      hA, PowerSeries.coeff_mk, RingHom.comp_apply, RingHom.coe_coe]

  obtain ⟨n, cv, r, hrV, hsum⟩ :=
    @PowerSeries.exists_map_eq_sum_smul_map_of_forall_map_algEquiv_mem ℂ _ _ ι
      (LinearMap.range (qExpL M H k)) K hKfin A hAK hV

  have hR : ∀ i, ∃ (R : ModularForm (ΓGL (CohCarrier.GammaH M H)) k) (D : ℤ)
      (p : PowerSeries ℤ), D ≠ 0 ∧ IsIntegralQExp (⇑((D : ℂ) • R)) p ∧
        qExpansion 1 ⇑R = (r i).map (algebraMap ℚ ℂ) := by
    intro i
    obtain ⟨R, hRq⟩ := hrV i
    rw [qExpL_apply] at hRq
    have hRrat : ∀ m : ℕ, ∃ q : ℚ, (qExpansion 1 ⇑(res1 R)).coeff m = (q : ℂ) := fun m =>
      ⟨PowerSeries.coeff m (r i), by rw [coe_res1, hRq, PowerSeries.coeff_map, eq_ratCast]⟩
    obtain ⟨D, p, hD, hp⟩ :=
      ModularCurve.exists_isIntegralQExp_smul_of_ratCast_qExpansion M (res1 R) hRrat
    exact ⟨R, D, p, hD, by rwa [coe_smul_form], hRq⟩
  choose R D p hD hp hRq using hR
  refine ⟨n, fun i => cv i / (D i : Qb), fun i => (D i : ℂ) • R i, p, hp, ?_⟩

  have hforms : frickeForm f = ∑ i, ι (cv i) • R i := by
    apply qExpL_injective
    rw [map_sum, qExpL_apply, coe_frickeForm, ← hAmap, hsum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, qExpL_apply, hRq]
  have hcoe := congrArg (fun F : ModularForm (ΓGL (CohCarrier.GammaH M H)) k =>
    (⇑F : UpperHalfPlane → ℂ)) hforms
  have hsumcoe :
      (⇑(∑ i, ι (cv i) • R i) : UpperHalfPlane → ℂ) = ∑ i, ⇑(ι (cv i) • R i) :=
    map_sum (FunLike.coeAddMonoidHom (ModularForm (ΓGL (CohCarrier.GammaH M H)) k) UpperHalfPlane ℂ)
      _ _
  simp only [coe_frickeForm, hsumcoe, coe_smul_form] at hcoe
  rw [hcoe]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coe_smul_form, smul_smul, map_div₀, map_intCast, div_mul_cancel₀ _ (by exact_mod_cast hD i)]

end Span

/-- **The Fricke slash of a form with rational `q`-expansion.** For a weight-`k` form `f` on
`Γ_H(M) = CohCarrier.GammaH M H` whose level-one `q`-expansion has rational coefficients,
and any `W ∈ GL(2, ℝ)` with `W = !![0, -1; M, 0]`, the slash `f ∣[k] W` is a finite
`ℚ̄`-linear combination `∑ i, ι (c i) • g i` of `Γ_H(M)`-forms `g i` that each admit an
integral `q`-expansion. -/
theorem exists_slash_fricke_eq_sum_smul_of_ratCast_qExpansion (M : ℕ) [NeZero M]
    (H : Subgroup (ZMod M)ˣ) {k : ℤ}
    (f : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k)
    (hf : ∀ n : ℕ, ∃ r : ℚ, (UpperHalfPlane.qExpansion 1 f).coeff n = (r : ℂ))
    (ι : AlgebraicClosure ℚ →+* ℂ) (W : GL (Fin 2) ℝ)
    (hW : (W : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; (M : ℝ), 0]) :
    ∃ (n : ℕ) (c : Fin n → AlgebraicClosure ℚ)
      (g : Fin n → ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k)
      (p : Fin n → PowerSeries ℤ), (∀ i, ModularCurve.IsIntegralQExp (g i) (p i)) ∧
        (⇑f : UpperHalfPlane → ℂ) ∣[k] W = ∑ i, ι (c i) • (⇑(g i) : UpperHalfPlane → ℂ) := by
  obtain rfl : W = frickeGL M := eq_frickeGL hW
  exact exists_slash_frickeGL_eq_sum ι f hf

end ModularCurve
