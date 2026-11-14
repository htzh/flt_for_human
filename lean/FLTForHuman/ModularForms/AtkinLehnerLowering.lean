/-
  Atkin--Lehner level lowering: the `Γ₁` depletion, and vanishing of the coefficients off `K`
  forcing a lower level.

  * `CuspForm.exists_gamma1_qCoeff_eq_ite_coprime`: a `Γ₁(N)`-cusp form of weight `k` is depleted
    at `Q` -- for `N * Q ^ 2 ∣ M` there is a `Γ₁(M)`-cusp form whose `n`-th coefficient is the
    original one exactly at the indices coprime to `Q` and zero elsewhere.  The construction is the
    average of the translates `f ∣[k] (S T^{j M / Q} S⁻¹)` over `j < Q` (`depleteForm`) plus the
    level restriction `Γ₁(N * Q ^ 2) → Γ₁(M)`; the coefficient computation is the exponential-sum
    identity `sum_exp_two_pi_mul`.
  * `CuspForm.qCoeff_eq_zero_of_coprime_level_of_forall_coprime_qCoeff_eq_zero`: the intermediate
    criterion -- a form whose coefficients vanish at every index prime to `K` also has them vanish at
    every index prime to the level `N`, by applying the depletion at each prime not dividing `N`.
  * `CuspForm.exists_qCoeff_eq_sum_primeFactors_of_forall_coprime_qCoeff_eq_zero`: the Atkin--Lehner
    conclusion -- such a form is the sum, over the primes dividing `N`, of the `p`-th subsequences of
    forms at the levels `Γ₁(N / p)`.  The decomposition uses the Atkin--Lehner operator `w_ε`
    (`wGL`), the average `avgV` of the level-`p` translations, and the degeneracy lift
    (`exists_degeneracy_gamma1_hasNebentypus`, ported).

  Transcribed from the pin's proof files (pinned `aa2d8b3`)
  `P2M/Sol/S_CuspForm_exists_gamma1_qCoeff_eq_ite_coprime.lean` (339 lines, 28 declarations),
  `S_CuspForm_qCoeff_eq_zero_of_coprime_level_of_forall_coprime_qCoeff_eq_zero.lean` (118 lines, 4
  declarations) and
  `S_CuspForm_exists_qCoeff_eq_sum_primeFactors_of_forall_coprime_qCoeff_eq_zero.lean` (868 lines, 76
  declarations), with the statements from the wrappers of the same names.  The third file copies the
  first's 25-line prelude block (`intCast_zmod_eq_one_iff_dvd`, `transGL`, `restrictLevel`,
  `translate`, `depleteForm`, `hasSum_qExp`, the `Γ₁`-monotonicity lemmas) verbatim; those
  declarations are written **once**, in the first namespace, and the third reuses them.  The pin's
  label namespaces are rectified: `CuspFormDepletionSol` -> `Depletion`, `CoprimeLevelSol` ->
  `CoprimeLevel`, `ALMainSol` -> `AtkinLehnerMain`.

  Assumes from earlier modules: `ModularForms/HeckeDiagDegeneracy.lean` (the degeneracy lift and the
  prime-coefficient criterion) and `ModularForms/NebentypusSeparation.lean` (the level-`N / p`
  separation of a `Γ₁(N)`-invariant sum).

  spec-pin: Theorems/Thm_CuspForm_exists_gamma1_qCoeff_eq_ite_coprime.lean
  spec-pin: P2M/Sol/S_CuspForm_exists_gamma1_qCoeff_eq_ite_coprime.lean
  spec-pin: Theorems/Thm_CuspForm_qCoeff_eq_zero_of_coprime_level_of_forall_coprime_qCoeff_eq_zero.lean
  spec-pin: P2M/Sol/S_CuspForm_qCoeff_eq_zero_of_coprime_level_of_forall_coprime_qCoeff_eq_zero.lean
  spec-pin: Theorems/Thm_CuspForm_exists_qCoeff_eq_sum_primeFactors_of_forall_coprime_qCoeff_eq_zero.lean
  spec-pin: P2M/Sol/S_CuspForm_exists_qCoeff_eq_sum_primeFactors_of_forall_coprime_qCoeff_eq_zero.lean
-/
import FLTForHuman.ModularForms.HeckeDiagDegeneracy
import FLTForHuman.ModularForms.NebentypusSeparation
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.NumberTheory.Modular
import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section


namespace Depletion

open CongruenceSubgroup ModularForm SlashInvariantForm Matrix MatrixGroups Function OnePoint Complex Function.Complex Matrix.SpecialLinearGroup Matrix.GeneralLinearGroup
open UpperHalfPlane hiding I
open scoped Real

local notation "𝕢" => Function.Periodic.qParam

lemma intCast_zmod_eq_one_iff_dvd (x : ℤ) (N : ℕ) :
    ((x : ℤ) : ZMod N) = 1 ↔ (N : ℤ) ∣ x - 1 := by
  rw [← sub_eq_zero, ← Int.cast_one, ← Int.cast_sub, ZMod.intCast_zmod_eq_zero_iff_dvd]

lemma Gamma1_le_of_dvd {A B : ℕ} (h : A ∣ B) : Gamma1 B ≤ Gamma1 A := by
  intro γ hγ
  rw [Gamma1_mem] at hγ ⊢
  obtain ⟨h1, h2, h3⟩ := hγ
  have hAB : (A : ℤ) ∣ (B : ℤ) := Int.natCast_dvd_natCast.mpr h
  refine ⟨?_, ?_, ?_⟩
  · rw [intCast_zmod_eq_one_iff_dvd] at h1 ⊢; exact hAB.trans h1
  · rw [intCast_zmod_eq_one_iff_dvd] at h2 ⊢; exact hAB.trans h2
  · rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h3 ⊢; exact hAB.trans h3

lemma GammaOneGL_le_of_dvd {A B : ℕ} (h : A ∣ B) :
    ((Gamma1 B : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤
      ((Gamma1 A : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) :=
  Subgroup.map_mono (Gamma1_le_of_dvd h)

abbrev transGL (t : ℝ) : GL (Fin 2) ℝ := upperRightHom t

lemma val_transGL (t : ℝ) :
    ((transGL t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![1, t; 0, 1] := by
  simp [transGL]

lemma intCast_zmod_eq_one_of_dvd {N : ℕ} {x : ℤ} (h : (N : ℤ) ∣ x - 1) :
    ((x : ℤ) : ZMod N) = 1 :=
  (intCast_zmod_eq_one_iff_dvd x N).mpr h

lemma exists_cocycle_trans {N ℓ : ℕ} (hℓ : ℓ ≠ 0) (j : ℤ) {γ : SL(2, ℤ)}
    (hγ : γ ∈ Gamma1 (N * ℓ ^ 2)) :
    ∃ δ : SL(2, ℤ), δ ∈ Gamma1 N ∧
      transGL ((j : ℝ) / ℓ) * mapGL ℝ γ = mapGL ℝ δ * transGL ((j : ℝ) / ℓ) := by
  rw [Gamma1_mem] at hγ
  obtain ⟨ha, hd, hc⟩ := hγ
  have hdet : (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 -
      (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 1 := by
    have := γ.det_coe; rwa [Matrix.det_fin_two] at this

  have hNl_c : ((N * ℓ ^ 2 : ℕ) : ℤ) ∣ (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hc
  have hNl_a : ((N * ℓ ^ 2 : ℕ) : ℤ) ∣ (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [ha, sub_self]
  have hNl_d : ((N * ℓ ^ 2 : ℕ) : ℤ) ∣ (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [hd, sub_self]
  have hN_Nl : (N : ℤ) ∣ ((N * ℓ ^ 2 : ℕ) : ℤ) := ⟨ℓ ^ 2, by push_cast; ring⟩
  have hl_Nl : (ℓ : ℤ) ∣ ((N * ℓ ^ 2 : ℕ) : ℤ) := ⟨N * ℓ, by push_cast; ring⟩
  have hl2_Nl : ((ℓ : ℤ) ^ 2) ∣ ((N * ℓ ^ 2 : ℕ) : ℤ) := ⟨N, by push_cast; ring⟩
  obtain ⟨c₂, hc₂⟩ : ((ℓ : ℤ) ^ 2) ∣ (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := hl2_Nl.trans hNl_c
  obtain ⟨e, he⟩ : (ℓ : ℤ) ∣
      (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 - (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 := by
    have := dvd_sub (hl_Nl.trans hNl_d) (hl_Nl.trans hNl_a)
    convert this using 1; first | rfl | ring
  have hN_c₂ : (N : ℤ) ∣ c₂ := by
    obtain ⟨q, hq⟩ := hNl_c
    refine ⟨q, ?_⟩
    have hℓ' : ((ℓ : ℤ) ^ 2) ≠ 0 := pow_ne_zero 2 (by exact_mod_cast hℓ)
    apply mul_left_cancel₀ hℓ'
    rw [← hc₂, hq]; push_cast; ring

  set a : ℤ := (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 with ha'
  set b : ℤ := (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 with hb'
  set c : ℤ := (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 with hc'
  set d : ℤ := (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 with hd'
  have hdetδ : Matrix.det !![a + j * ℓ * c₂, b + j * e - j ^ 2 * c₂; c, d - j * ℓ * c₂] = 1 := by
    rw [Matrix.det_fin_two_of]
    linear_combination hdet + (j * ℓ * c₂) * he + (j ^ 2 * c₂ - j * e) * hc₂
  let δ : SL(2, ℤ) :=
    ⟨!![a + j * ℓ * c₂, b + j * e - j ^ 2 * c₂; c, d - j * ℓ * c₂], hdetδ⟩
  have hδcoe : (δ : Matrix (Fin 2) (Fin 2) ℤ)
      = !![a + j * ℓ * c₂, b + j * e - j ^ 2 * c₂; c, d - j * ℓ * c₂] := rfl
  refine ⟨δ, ?_, ?_⟩
  · rw [Gamma1_mem]
    simp only [hδcoe, of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
      cons_val_fin_one]
    have hN_lc₂ : (N : ℤ) ∣ ℓ * c₂ := dvd_mul_of_dvd_right hN_c₂ _
    refine ⟨?_, ?_, ?_⟩
    · apply intCast_zmod_eq_one_of_dvd
      have := dvd_add (hN_Nl.trans hNl_a) (dvd_mul_of_dvd_right hN_lc₂ j)
      convert this using 1; first | rfl | ring
    · apply intCast_zmod_eq_one_of_dvd
      have := dvd_sub (hN_Nl.trans hNl_d) (dvd_mul_of_dvd_right hN_lc₂ j)
      convert this using 1; first | rfl | ring
    · exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (hN_Nl.trans hNl_c)
  ·
    have hℓR : (ℓ : ℝ) ≠ 0 := by exact_mod_cast hℓ
    have hdR : (d : ℝ) = a + ℓ * e := by
      have : ((d - a : ℤ) : ℝ) = ((ℓ * e : ℤ) : ℝ) := congrArg (Int.cast) he
      push_cast at this; linarith
    have hcR : (c : ℝ) = (ℓ : ℝ) ^ 2 * c₂ := by exact_mod_cast hc₂
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, val_transGL, mapGL_coe_matrix, mapGL_coe_matrix]
    ext i j'
    fin_cases i <;> fin_cases j' <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, hδcoe, ← ha', ← hb', ← hc', ← hd', hcR, hdR] <;>
      field_simp <;> ring

def restrictLevel {A B : ℕ} (h : A ∣ B) {k : ℤ} (f : CuspForm (Gamma1 A) k) :
    CuspForm (Gamma1 B) k where
  toFun := ⇑f
  slash_action_eq' γ hγ := SlashInvariantFormClass.slash_action_eq f γ (GammaOneGL_le_of_dvd h hγ)
  holo' := CuspFormClass.holo f
  zero_at_cusps' hc := CuspFormClass.zero_at_cusps f (hc.mono (GammaOneGL_le_of_dvd h))

@[scoped simp] lemma coe_restrictLevel {A B : ℕ} (h : A ∣ B) {k : ℤ} (f : CuspForm (Gamma1 A) k) :
    ⇑(restrictLevel h f) = ⇑f := rfl

lemma slash_transGL_apply (f : ℍ → ℂ) (k : ℤ) (t : ℝ) (τ : ℍ) :
    (f ∣[k] transGL t) τ = f (t +ᵥ τ) := by
  have hsm : transGL t • τ = t +ᵥ τ := by
    ext
    simp [transGL, σ, num, denom, coe_vadd, UpperHalfPlane.coe_smul, add_comm]
  rw [slash_apply, hsm]
  simp [transGL, σ, denom, GeneralLinearGroup.val_det_apply]

def transGLRat (q : ℚ) : GL (Fin 2) ℚ := upperRightHom q

lemma transGLRat_map (q : ℚ) :
    (transGLRat q).map (Rat.castHom ℝ) = transGL (q : ℝ) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [transGLRat, transGL]

lemma isCusp_SL2Z_ratSmul {c : OnePoint ℝ} (hc : IsCusp c 𝒮ℒ) (gQ : GL (Fin 2) ℚ) :
    IsCusp (gQ.map (Rat.castHom ℝ) • c) 𝒮ℒ := by
  rw [isCusp_SL2Z_iff] at hc ⊢
  obtain ⟨c₀, rfl⟩ := hc
  exact ⟨gQ • c₀, by rw [← Rat.coe_castHom, OnePoint.map_smul]⟩

def translate {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm (Gamma1 N) k) {ℓ : ℕ} (hℓ : ℓ ≠ 0)
    (j : ℤ) : CuspForm (Gamma1 (N * ℓ ^ 2)) k where
  toFun := ⇑f ∣[k] transGL ((j : ℝ) / ℓ)
  slash_action_eq' γ hγ := by
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hγ
    obtain ⟨δ, hδ, hcoc⟩ := exists_cocycle_trans (N := N) hℓ j hg
    rw [← SlashAction.slash_mul, hcoc, SlashAction.slash_mul,
      SlashInvariantFormClass.slash_action_eq f (mapGL ℝ δ) (Subgroup.mem_map.mpr ⟨δ, hδ, rfl⟩)]
  holo' := (CuspFormClass.holo f).slash k _
  zero_at_cusps' {c} hc := by
    have : NeZero (N * ℓ ^ 2) := ⟨mul_ne_zero (NeZero.ne N) (pow_ne_zero 2 hℓ)⟩
    refine IsZeroAt.smul_iff.mp (CuspFormClass.zero_at_cusps f ?_)
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc ⊢
    have : transGL ((j : ℝ) / ℓ) = (transGLRat ((j : ℚ) / ℓ)).map (Rat.castHom ℝ) := by
      rw [transGLRat_map]; push_cast; rfl
    rw [this]
    exact isCusp_SL2Z_ratSmul hc _

@[scoped simp] lemma translate_apply {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm (Gamma1 N) k) {ℓ : ℕ}
    (hℓ : ℓ ≠ 0) (j : ℤ) (τ : ℍ) :
    translate f hℓ j τ = f ((((j : ℝ) / ℓ : ℝ)) +ᵥ τ) :=
  slash_transGL_apply _ _ _ _

lemma one_mem_strictPeriods_Gamma1 (L : ℕ) :
    (1 : ℝ) ∈ ((Gamma1 L : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [strictPeriods_Gamma1]; exact AddSubgroup.mem_zmultiples 1

lemma hasSum_qExp {L : ℕ} [NeZero L] {k : ℤ} (F : CuspForm (Gamma1 L) k) (τ : ℍ) :
    HasSum (fun n : ℕ => (qExpansion 1 ⇑F).coeff n • 𝕢 1 τ ^ n) (F τ) :=
  hasSum_qExpansion F one_pos (one_mem_strictPeriods_Gamma1 L) τ

lemma qParam_vadd (t : ℝ) (τ : ℍ) :
    𝕢 1 ((t +ᵥ τ : ℍ) : ℂ) = cexp (2 * π * I * t) * 𝕢 1 τ := by
  simp only [Periodic.qParam, coe_vadd, ← Complex.exp_add]
  congr 1; push_cast; ring

lemma sum_exp_two_pi_mul (ℓ : ℕ) (hℓ : ℓ ≠ 0) (n : ℕ) :
    ∑ j ∈ Finset.range ℓ, cexp (2 * π * I * (((j : ℤ) : ℝ) / ℓ : ℝ)) ^ n
      = if ℓ ∣ n then (ℓ : ℂ) else 0 := by
  have hℓC : (ℓ : ℂ) ≠ 0 := by exact_mod_cast hℓ
  set ζ : ℂ := cexp (2 * π * I * (n / ℓ)) with hζ
  have hterm : ∀ j : ℕ, cexp (2 * π * I * (((j : ℤ) : ℝ) / ℓ : ℝ)) ^ n = ζ ^ j := by
    intro j
    rw [hζ, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
    congr 1; push_cast; ring
  simp_rw [hterm]
  split_ifs with hdvd
  · obtain ⟨m, rfl⟩ := hdvd
    have hζ1 : ζ = 1 := by
      rw [hζ]; push_cast
      rw [show 2 * (π : ℂ) * I * ((ℓ : ℂ) * m / ℓ) = m * (2 * π * I) by field_simp]
      exact Complex.exp_nat_mul_two_pi_mul_I m
    simp [hζ1]
  · have hζne : ζ ≠ 1 := by
      intro h
      rw [hζ, Complex.exp_eq_one_iff] at h
      obtain ⟨m, hm⟩ := h
      have h2 : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
      have hnm : (n : ℂ) = m * ℓ := by
        have h3 : (2 * π * I : ℂ) * (n / ℓ) = (2 * π * I) * m := by rw [hm]; ring
        have h4 := mul_left_cancel₀ h2 h3
        field_simp at h4
        linear_combination h4
      have hnmZ : (n : ℤ) = m * ℓ := by exact_mod_cast hnm
      exact hdvd (Int.natCast_dvd_natCast.mp ⟨m, by rw [hnmZ]; ring⟩)
    have hζℓ : ζ ^ ℓ = 1 := by
      rw [hζ, ← Complex.exp_nat_mul]
      rw [show (ℓ : ℂ) * (2 * π * I * (n / ℓ)) = n * (2 * π * I) by field_simp]
      exact Complex.exp_nat_mul_two_pi_mul_I n
    rw [geom_sum_eq hζne, hζℓ, sub_self, zero_div]

lemma coe_finset_sum {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} {ι : Type*} (s : Finset ι)
    (F : ι → CuspForm Γ k) : ⇑(∑ i ∈ s, F i) = ∑ i ∈ s, ⇑(F i) :=
  FunLike.coe_sum s F

def depleteForm {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm (Gamma1 N) k) {ℓ : ℕ} (hℓ : ℓ ≠ 0) :
    CuspForm (Gamma1 (N * ℓ ^ 2)) k :=
  restrictLevel (dvd_mul_right N (ℓ ^ 2)) f -
    (ℓ : ℂ)⁻¹ • ∑ j ∈ Finset.range ℓ, translate f hℓ (j : ℤ)

lemma depleteForm_apply {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm (Gamma1 N) k) {ℓ : ℕ}
    (hℓ : ℓ ≠ 0) (τ : ℍ) :
    depleteForm f hℓ τ
      = f τ - (ℓ : ℂ)⁻¹ * ∑ j ∈ Finset.range ℓ, f (((((j : ℤ) : ℝ) / ℓ : ℝ)) +ᵥ τ) := by
  simp only [depleteForm, FunLike.coe_sub, Pi.sub_apply, FunLike.coe_smul,
    Pi.smul_apply, coe_finset_sum, Finset.sum_apply, coe_restrictLevel, translate_apply,
    smul_eq_mul]

lemma hasSum_depleteForm {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm (Gamma1 N) k) {ℓ : ℕ}
    (hℓ : ℓ ≠ 0) (τ : ℍ) :
    HasSum (fun n : ℕ => (if ℓ ∣ n then 0 else (qExpansion 1 ⇑f).coeff n) • 𝕢 1 τ ^ n)
      (depleteForm f hℓ τ) := by
  have hℓC : (ℓ : ℂ) ≠ 0 := by exact_mod_cast hℓ
  set a : ℕ → ℂ := fun n => (qExpansion 1 ⇑f).coeff n with ha
  set e : ℕ → ℂ := fun j => cexp (2 * π * I * (((j : ℤ) : ℝ) / ℓ : ℝ)) with he

  have htr : ∀ j ∈ Finset.range ℓ,
      HasSum (fun n : ℕ => (a n * e j ^ n) • 𝕢 1 τ ^ n) (f (((((j : ℤ) : ℝ) / ℓ : ℝ)) +ᵥ τ)) := by
    intro j _
    have h := hasSum_qExp f (((((j : ℤ) : ℝ) / ℓ : ℝ)) +ᵥ τ)
    rw [qParam_vadd] at h
    convert h using 2 with n; try rfl
    simp only [ha, he, smul_eq_mul, mul_pow]; ring
  have hsum := (hasSum_qExp f τ).sub ((hasSum_sum htr).mul_left ((ℓ : ℂ)⁻¹))
  rw [← depleteForm_apply f hℓ τ] at hsum
  convert hsum using 2 with n; try rfl

  have hS := sum_exp_two_pi_mul ℓ hℓ n
  simp only [smul_eq_mul]
  rw [show ∑ j ∈ Finset.range ℓ, a n * e j ^ n * 𝕢 1 ↑τ ^ n
      = a n * 𝕢 1 ↑τ ^ n * ∑ j ∈ Finset.range ℓ, e j ^ n by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by ring]
  simp only [he] at hS ⊢
  rw [hS]
  split_ifs with hdvd
  · field_simp; ring
  · ring

lemma qCoeff_depleteForm {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm (Gamma1 N) k) {ℓ : ℕ}
    (hℓ : ℓ ≠ 0) (n : ℕ) :
    ModularFormClass.qCoeff (depleteForm f hℓ) n
      = if ℓ ∣ n then 0 else ModularFormClass.qCoeff f n := by
  have : NeZero (N * ℓ ^ 2) := ⟨mul_ne_zero (NeZero.ne N) (pow_ne_zero 2 hℓ)⟩
  have := ModularFormClass.qExpansion_coeff_unique one_pos
    (one_mem_strictPeriods_Gamma1 (N * ℓ ^ 2)) (f := depleteForm f hℓ)
    (hasSum_depleteForm f hℓ) n
  exact this.symm

lemma exists_deplete_finset {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm (Gamma1 N) k)
    (P : Finset ℕ) (hP : ∀ ℓ ∈ P, ℓ ≠ 0) :
    ∃ (L : ℕ) (_ : NeZero L) (g : CuspForm (Gamma1 L) k),
      L ∣ N * ∏ ℓ ∈ P, ℓ ^ 2 ∧
      ∀ n, ModularFormClass.qCoeff g n
        = if (∀ ℓ ∈ P, ¬ ℓ ∣ n) then ModularFormClass.qCoeff f n else 0 := by
  classical
  induction P using Finset.induction_on with
  | empty =>
    refine ⟨N, inferInstance, f, by simp, fun n => by simp⟩
  | insert ℓ P hℓP ih =>
    obtain ⟨L, hL, g, hLdvd, hg⟩ := ih (fun ℓ' hℓ' => hP ℓ' (Finset.mem_insert_of_mem hℓ'))
    have hℓ : ℓ ≠ 0 := hP ℓ (Finset.mem_insert_self ℓ P)
    have : NeZero (L * ℓ ^ 2) := ⟨mul_ne_zero (NeZero.ne L) (pow_ne_zero 2 hℓ)⟩
    refine ⟨L * ℓ ^ 2, inferInstance, depleteForm g hℓ, ?_, fun n => ?_⟩
    · refine (mul_dvd_mul_right hLdvd (ℓ ^ 2)).trans (dvd_of_eq ?_)
      rw [Finset.prod_insert hℓP]; ring
    · rw [qCoeff_depleteForm, hg n]
      by_cases h1 : ℓ ∣ n
      · have h2 : ¬ (∀ ℓ' ∈ insert ℓ P, ¬ ℓ' ∣ n) :=
          fun h => h ℓ (Finset.mem_insert_self _ _) h1
        rw [ite_eq_left h1, ite_eq_right h2]
      · rw [ite_eq_right h1]
        have h2 : (∀ ℓ' ∈ P, ¬ ℓ' ∣ n) ↔ (∀ ℓ' ∈ insert ℓ P, ¬ ℓ' ∣ n) := by
          rw [Finset.forall_mem_insert]; exact ⟨fun h => ⟨h1, h⟩, fun h => h.2⟩
        exact if_congr h2 rfl rfl

lemma coprime_iff_forall_primeFactors {Q : ℕ} (hQ : Q ≠ 0) (n : ℕ) :
    n.Coprime Q ↔ ∀ ℓ ∈ Q.primeFactors, ¬ ℓ ∣ n := by
  constructor
  · intro h ℓ hℓ hℓn
    rw [Nat.mem_primeFactors] at hℓ
    have := Nat.dvd_gcd hℓn hℓ.2.1
    rw [h.gcd_eq_one, Nat.dvd_one] at this
    exact hℓ.1.one_lt.ne' this
  · intro h
    refine (Nat.coprime_of_dvd fun p hp hpQ hpn => ?_).symm
    exact h p (Nat.mem_primeFactors.mpr ⟨hp, hpQ, hQ⟩) hpn

theorem main (N : ℕ) [NeZero N] (k : ℤ) (f : CuspForm (Gamma1 N) k) (Q : ℕ) (hQ : Q ≠ 0)
    (M : ℕ) (hM : N * Q ^ 2 ∣ M) :
    ∃ g : CuspForm (Gamma1 M) k,
      ∀ n : ℕ, ModularFormClass.qCoeff g n =
        if n.Coprime Q then ModularFormClass.qCoeff f n else 0 := by
  obtain ⟨L, hL, g, hLdvd, hg⟩ := exists_deplete_finset f Q.primeFactors
    (fun ℓ hℓ => (Nat.prime_of_mem_primeFactors hℓ).ne_zero)
  have hprod : ∏ ℓ ∈ Q.primeFactors, ℓ ^ 2 ∣ Q ^ 2 := by
    rw [Finset.prod_pow]; exact pow_dvd_pow_of_dvd (Nat.prod_primeFactors_dvd Q) 2
  have hLM : L ∣ M := hLdvd.trans ((mul_dvd_mul_left N hprod).trans hM)
  refine ⟨restrictLevel hLM g, fun n => ?_⟩
  rw [show ModularFormClass.qCoeff (restrictLevel hLM g) n = ModularFormClass.qCoeff g n from rfl,
    hg n]
  exact if_congr (coprime_iff_forall_primeFactors hQ n).symm rfl rfl

end Depletion

open CongruenceSubgroup

theorem CuspForm.exists_gamma1_qCoeff_eq_ite_coprime (N : ℕ) [NeZero N] (k : ℤ)
    (f : CuspForm (Gamma1 N) k) (Q : ℕ) (hQ : Q ≠ 0) (M : ℕ) (hM : N * Q ^ 2 ∣ M) :
    ∃ g : CuspForm (Gamma1 M) k,
      ∀ n : ℕ, ModularFormClass.qCoeff g n =
        if n.Coprime Q then ModularFormClass.qCoeff f n else 0 :=
  Depletion.main N k f Q hQ M hM

namespace CoprimeLevel

open CongruenceSubgroup
open scoped MatrixGroups

variable {k : ℤ}

lemma qCoeff_zero_form (L : ℕ) (n : ℕ) :
    ModularFormClass.qCoeff (⇑(0 : CuspForm (Gamma1 L) k)) n = 0 := by
  show (UpperHalfPlane.qExpansion 1 ⇑(0 : CuspForm (Gamma1 L) k)).coeff n = 0
  rw [FunLike.coe_zero, UpperHalfPlane.qExpansion_zero]; simp

lemma forall_qCoeff_eq_zero_of_aux (Q : Finset ℕ) :
    ∀ (L : ℕ) [NeZero L] (h : CuspForm (Gamma1 L) k),
      (∀ q ∈ Q, q.Prime ∧ ¬ q ∣ L) →
      (∀ n : ℕ, (∀ q ∈ Q, ¬ q ∣ n) → ModularFormClass.qCoeff h n = 0) →
      ∀ n : ℕ, ModularFormClass.qCoeff h n = 0 := by
  classical
  induction Q using Finset.induction_on with
  | empty =>
    intro L _ h _ hh n
    exact hh n (fun q hq => (Finset.notMem_empty q hq).elim)
  | insert p Q hpQ ih =>
    intro L _ h hQ hh
    have hp : p.Prime := (hQ p (Finset.mem_insert_self p Q)).1
    have hpL : ¬ p ∣ L := (hQ p (Finset.mem_insert_self p Q)).2
    have : NeZero (L * p ^ 2) := ⟨mul_ne_zero (NeZero.ne L) (pow_ne_zero 2 hp.ne_zero)⟩

    obtain ⟨g, hg⟩ := CuspForm.exists_gamma1_qCoeff_eq_ite_coprime L k h p hp.ne_zero
      (L * p ^ 2) dvd_rfl
    have hQ' : ∀ q ∈ Q, q.Prime ∧ ¬ q ∣ L * p ^ 2 := by
      intro q hq
      have hq' := hQ q (Finset.mem_insert_of_mem hq)
      refine ⟨hq'.1, fun hdvd => ?_⟩
      rcases (Nat.Prime.dvd_mul hq'.1).mp hdvd with h1 | h1
      · exact hq'.2 h1
      · have := (Nat.prime_dvd_prime_iff_eq hq'.1 hp).mp (hq'.1.dvd_of_dvd_pow h1)
        exact hpQ (this ▸ hq)
    have hg0 : ∀ n : ℕ, (∀ q ∈ Q, ¬ q ∣ n) → ModularFormClass.qCoeff g n = 0 := by
      intro n hn
      rw [hg n]
      split_ifs with hcop
      · refine hh n fun q hq => ?_
        rcases Finset.mem_insert.mp hq with rfl | hq
        · exact (Nat.Prime.coprime_iff_not_dvd hp).mp hcop.symm
        · exact hn q hq
      · rfl
    have hgall : ∀ n, ModularFormClass.qCoeff g n = 0 := ih (L * p ^ 2) g hQ' hg0

    have hsupp : ∀ n : ℕ, ¬ p ∣ n → ModularFormClass.qCoeff h n = 0 := by
      intro n hn
      have := hgall n
      rw [hg n, ite_eq_left (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).mpr hn))] at this
      exact this
    have h0 : h = 0 := CuspForm.gamma1_eq_zero_of_prime_not_dvd_of_qCoeff_eq_zero k hp hpL h hsupp
    intro n
    rw [h0]
    exact qCoeff_zero_form L n

theorem main (N : ℕ) [NeZero N] (K : ℕ) (hK : K ≠ 0) (f : CuspForm (Gamma1 N) k)
    (hf : ∀ n : ℕ, Nat.Coprime n K → ModularFormClass.qCoeff f n = 0)
    (n : ℕ) (hn : Nat.Coprime n N) : ModularFormClass.qCoeff f n = 0 := by
  classical
  have : NeZero (N * N ^ 2) := ⟨mul_ne_zero (NeZero.ne N) (pow_ne_zero 2 (NeZero.ne N))⟩

  obtain ⟨g, hg⟩ := CuspForm.exists_gamma1_qCoeff_eq_ite_coprime N k f N (NeZero.ne N)
    (N * N ^ 2) dvd_rfl

  set Q : Finset ℕ := K.primeFactors.filter (fun q => ¬ q ∣ N) with hQdef
  have hQ : ∀ q ∈ Q, q.Prime ∧ ¬ q ∣ N * N ^ 2 := by
    intro q hq
    rw [hQdef, Finset.mem_filter] at hq
    have hqpr : q.Prime := Nat.prime_of_mem_primeFactors hq.1
    refine ⟨hqpr, fun hdvd => hq.2 ?_⟩
    rcases (Nat.Prime.dvd_mul hqpr).mp hdvd with h1 | h1
    · exact h1
    · exact hqpr.dvd_of_dvd_pow h1
  have hg0 : ∀ m : ℕ, (∀ q ∈ Q, ¬ q ∣ m) → ModularFormClass.qCoeff g m = 0 := by
    intro m hm
    rw [hg m]
    split_ifs with hcop
    · apply hf
      refine Nat.coprime_of_dvd fun q hq hqm hqK => ?_
      by_cases hqN : q ∣ N
      · exact (Nat.Prime.coprime_iff_not_dvd hq).mp (Nat.Coprime.coprime_dvd_left hqm hcop) hqN
      · have hqQ : q ∈ Q := by
          rw [hQdef, Finset.mem_filter]
          exact ⟨Nat.mem_primeFactors.mpr ⟨hq, hqK, hK⟩, hqN⟩
        exact hm q hqQ hqm
    · rfl
  have hgall := forall_qCoeff_eq_zero_of_aux Q (N * N ^ 2) g hQ hg0
  have := hgall n
  rw [hg n, ite_eq_left hn] at this
  exact this

end CoprimeLevel

open CongruenceSubgroup
open scoped MatrixGroups

theorem CuspForm.qCoeff_eq_zero_of_coprime_level_of_forall_coprime_qCoeff_eq_zero
    (N : ℕ) [NeZero N] (k : ℤ) (K : ℕ) (hK : K ≠ 0) (f : CuspForm (Gamma1 N) k)
    (hf : ∀ n : ℕ, Nat.Coprime n K → ModularFormClass.qCoeff f n = 0)
    (n : ℕ) (hn : Nat.Coprime n N) : ModularFormClass.qCoeff f n = 0 :=
  CoprimeLevel.main N K hK f hf n hn

namespace AtkinLehnerMain

open Depletion

open CongruenceSubgroup ModularForm SlashInvariantForm Matrix MatrixGroups Function OnePoint Matrix.SpecialLinearGroup Matrix.GeneralLinearGroup

open _root_.Complex hiding Gamma
open UpperHalfPlane hiding I
open scoped Real ModularForm

local notation "𝕢" => Function.Periodic.qParam
local notation "Γ₁(" M ")" => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))
local notation "𝒢(" M ")" =>
  ((CongruenceSubgroup.Gamma M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

def wGL (M : ℕ) (hM : M ≠ 0) (ε : ℝ) (hε : ε ≠ 0) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, -ε; ε * M, 0]
    (by
      rw [Matrix.det_fin_two_of]
      have hM' : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero hM
      have : (0 : ℝ) * 0 - -ε * (ε * M) = ε ^ 2 * M := by ring
      rw [this]; positivity)

@[scoped simp] lemma val_wGL (M : ℕ) (hM : M ≠ 0) (ε : ℝ) (hε : ε ≠ 0) :
    ((wGL M hM ε hε : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![0, -ε; ε * M, 0] := rfl

lemma det_wGL (M : ℕ) (hM : M ≠ 0) (ε : ℝ) (hε : ε ≠ 0) :
    ((wGL M hM ε hε).det : ℝ) = ε ^ 2 * M := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, val_wGL, Matrix.det_fin_two_of]; ring

lemma det_wGL_pos (M : ℕ) (hM : M ≠ 0) (ε : ℝ) (hε : ε ≠ 0) :
    0 < ((wGL M hM ε hε).det : ℝ) := by
  rw [det_wGL]; have : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero hM
  positivity

local notation "W[" M "]" => wGL M (NeZero.ne M) 1 one_ne_zero

local notation "W'[" M "," h "]" => wGL M h (-1) (neg_ne_zero.mpr one_ne_zero)

def lowU (m : ℤ) : SL(2, ℤ) := ModularGroup.S * ModularGroup.T ^ m * ModularGroup.S⁻¹

lemma coe_lowU (m : ℤ) : (lowU m : Matrix (Fin 2) (Fin 2) ℤ) = !![1, 0; -m, 1] := by
  rw [lowU, ModularGroup.S_inv, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T_zpow, Matrix.SpecialLinearGroup.coe_neg,
    ModularGroup.coe_S]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

lemma lowU_apply (m : ℤ) (i j : Fin 2) : (lowU m) i j = !![(1 : ℤ), 0; -m, 1] i j := by
  rw [← coe_lowU]

lemma lowU_add (m m' : ℤ) : lowU (m + m') = lowU m * lowU m' := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_lowU, coe_lowU, coe_lowU]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]; ring

lemma lowU_zero : lowU 0 = 1 := by
  ext i j
  rw [coe_lowU, Matrix.SpecialLinearGroup.coe_one]
  fin_cases i <;> fin_cases j <;> simp

lemma lowU_natMul (m : ℤ) (b : ℕ) : lowU (b * m) = lowU m ^ b := by
  induction b with
  | zero => simp [lowU_zero]
  | succ b ih => rw [pow_succ, ← ih, ← lowU_add]; congr 1; push_cast; ring

lemma lowU_mem_Gamma (N : ℕ) : lowU (N : ℤ) ∈ CongruenceSubgroup.Gamma N := by
  rw [Gamma_mem]
  simp [lowU_apply]

lemma val_mapGL_eq (g : SL(2, ℤ)) :
    ((mapGL ℝ g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      = !![((g 0 0 : ℤ) : ℝ), ((g 0 1 : ℤ) : ℝ); ((g 1 0 : ℤ) : ℝ), ((g 1 1 : ℤ) : ℝ)] := by
  ext i j
  rw [mapGL_coe_matrix]
  fin_cases i <;> fin_cases j <;> simp

lemma wGL_mul_lowU (M : ℕ) (hM : M ≠ 0) (ε : ℝ) (hε : ε ≠ 0) (m : ℤ) :
    wGL M hM ε hε * mapGL ℝ (lowU m) = transGL ((m : ℝ) / M) * wGL M hM ε hε := by
  have hM' : (M : ℝ) ≠ 0 := by exact_mod_cast hM
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, val_wGL, val_transGL, val_mapGL_eq]
  simp only [lowU_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]; field_simp

lemma wGL_mul_wGL (N : ℕ) (hN : N ≠ 0) :
    wGL N hN 1 one_ne_zero * wGL N hN (-1) (neg_ne_zero.mpr one_ne_zero)
      = Matrix.GeneralLinearGroup.mkOfDetNeZero ((N : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ))
          (by rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]; positivity) := by
  apply Units.ext
  rw [Units.val_mul, val_wGL, val_wGL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply]

lemma wGL_eq_wGL_mul_heckeDiagMatrix {N M p : ℕ} (hN : N ≠ 0) (hM : M ≠ 0) (hp : p ≠ 0)
    (h : M * p = N) :
    wGL N hN (-1) (neg_ne_zero.mpr one_ne_zero)
      = wGL M hM (-1) (neg_ne_zero.mpr one_ne_zero) * heckeDiagMatrix p := by
  apply Units.ext
  rw [Units.val_mul, val_wGL, val_wGL, val_heckeDiagMatrix hp]
  have : (N : ℝ) = M * p := by exact_mod_cast h.symm
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, this]

lemma slash_scalar (N : ℕ) (hN : N ≠ 0) (k : ℤ) (f : ℍ → ℂ) :
    f ∣[k] (Matrix.GeneralLinearGroup.mkOfDetNeZero ((N : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ))
          (by rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]; positivity))
      = ((N : ℂ) ^ (k - 2)) • f := by
  set g := Matrix.GeneralLinearGroup.mkOfDetNeZero ((N : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ))
          (by rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]; positivity) with hg
  have hdet : (g.det : ℝ) = (N : ℝ) * N := by
    rw [Matrix.GeneralLinearGroup.val_det_apply]; simp [hg, Fintype.card_fin, pow_two]
  have hdetpos : (0 : ℝ) < (N : ℝ) * N := by positivity
  have hσ : UpperHalfPlane.σ g = .refl ℝ ℂ := by
    rw [UpperHalfPlane.σ, ite_eq_left (by rw [hdet]; exact hdetpos)]
  funext τ
  have hsmul : g • τ = τ := by
    apply UpperHalfPlane.ext
    rw [UpperHalfPlane.coe_smul_of_det_pos (by rw [hdet]; exact hdetpos)]
    have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN
    simp [UpperHalfPlane.num, UpperHalfPlane.denom, hg, Matrix.smul_apply]
    field_simp
  rw [ModularForm.slash_apply, Pi.smul_apply, smul_eq_mul, hσ, hdet, hsmul]
  simp only [ContinuousAlgEquiv.refl_apply]
  have hden : UpperHalfPlane.denom g (τ : ℂ) = N := by
    simp [UpperHalfPlane.denom, hg, Matrix.smul_apply]
  rw [hden, abs_of_pos hdetpos]
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  push_cast
  have key : ((N : ℂ) * N) ^ (k - 1) * (N : ℂ) ^ (-k) = (N : ℂ) ^ (k - 2) := by
    rw [show (N : ℂ) * N = (N : ℂ) ^ (2 : ℤ) by rw [zpow_two], ← _root_.zpow_mul,
      ← zpow_add₀ hN']
    congr 1; ring
  rw [mul_assoc, key, mul_comm]

lemma slash_wGL_apply (M : ℕ) (hM : M ≠ 0) (ε : ℝ) (hε : ε ≠ 0) (k : ℤ) (f : ℍ → ℂ) (τ : ℍ) :
    (f ∣[k] wGL M hM ε hε) τ
      = f (wGL M hM ε hε • τ) * ((((wGL M hM ε hε).det : ℝ) : ℂ) ^ (k - 1) *
          UpperHalfPlane.denom (wGL M hM ε hε) τ ^ (-k)) := by
  rw [ModularForm.slash_apply]
  have hσ : UpperHalfPlane.σ (wGL M hM ε hε) = .refl ℝ ℂ := by
    rw [UpperHalfPlane.σ, ite_eq_left (det_wGL_pos M hM ε hε)]
  rw [hσ, abs_of_pos (det_wGL_pos M hM ε hε)]
  simp only [ContinuousAlgEquiv.refl_apply]
  ring

lemma sub_slash_wGL (M : ℕ) (hM : M ≠ 0) (ε : ℝ) (hε : ε ≠ 0) (k : ℤ) (f g : ℍ → ℂ) :
    (f - g) ∣[k] wGL M hM ε hε = f ∣[k] wGL M hM ε hε - g ∣[k] wGL M hM ε hε := by
  funext τ; simp only [slash_wGL_apply, Pi.sub_apply]; ring

lemma smul_slash_wGL (M : ℕ) (hM : M ≠ 0) (ε : ℝ) (hε : ε ≠ 0) (k : ℤ) (c : ℂ) (f : ℍ → ℂ) :
    (c • f) ∣[k] wGL M hM ε hε = c • (f ∣[k] wGL M hM ε hε) := by
  funext τ; simp only [slash_wGL_apply, Pi.smul_apply, smul_eq_mul]; ring

lemma sum_slash_wGL (M : ℕ) (hM : M ≠ 0) (ε : ℝ) (hε : ε ≠ 0) (k : ℤ) {ι : Type*}
    (s : Finset ι) (f : ι → ℍ → ℂ) :
    (∑ i ∈ s, f i) ∣[k] wGL M hM ε hε = ∑ i ∈ s, (f i ∣[k] wGL M hM ε hε) := by
  funext τ
  simp only [slash_wGL_apply, Finset.sum_apply, Finset.sum_mul]

lemma exists_cocycle_wGL (M : ℕ) (hM : M ≠ 0) (ε : ℝ) (hε : ε ≠ 0) {γ : SL(2, ℤ)}
    (hγ : γ ∈ Gamma1 M) :
    ∃ γ' : SL(2, ℤ), γ' ∈ Gamma1 M ∧
      wGL M hM ε hε * mapGL ℝ γ = mapGL ℝ γ' * wGL M hM ε hε := by
  rw [Gamma1_mem] at hγ
  obtain ⟨ha, hd, hc⟩ := hγ
  have hdet : (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 -
      (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 1 := by
    have := γ.det_coe; rwa [Matrix.det_fin_two] at this
  obtain ⟨c₁, hc₁⟩ : (M : ℤ) ∣ (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hc
  have hdet' : Matrix.det !![(γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1, -c₁;
      -(M : ℤ) * (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1, (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0] = 1 := by
    rw [Matrix.det_fin_two_of]; linear_combination hdet + (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * hc₁
  let γ' : SL(2, ℤ) :=
    ⟨!![(γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1, -c₁;
      -(M : ℤ) * (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1, (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0], hdet'⟩
  have hγ'coe : (γ' : Matrix (Fin 2) (Fin 2) ℤ) = !![(γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1, -c₁;
      -(M : ℤ) * (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1, (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0] := rfl
  refine ⟨γ', ?_, ?_⟩
  · rw [Gamma1_mem]
    simp only [hγ'coe, of_apply, cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one]
    refine ⟨hd, ha, ?_⟩
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact ⟨-(γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1, by ring⟩
  · have hcR : (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ℝ) = M * c₁ := by exact_mod_cast hc₁
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, val_wGL, val_mapGL_eq, val_mapGL_eq]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, hcR, hγ'coe] <;> ring

def wGLRat (M : ℕ) (ε : ℤ) (h : (ε : ℚ) * (ε : ℚ) * M ≠ 0) : GL (Fin 2) ℚ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, -(ε : ℚ); (ε : ℚ) * M, 0]
    (by rw [Matrix.det_fin_two_of]; convert h using 1; ring)

lemma wGLRat_map (M : ℕ) (hM : M ≠ 0) (ε : ℤ) (hε : (ε : ℝ) ≠ 0)
    (h : (ε : ℚ) * (ε : ℚ) * M ≠ 0) :
    (wGLRat M ε h).map (Rat.castHom ℝ) = wGL M hM (ε : ℝ) hε := by
  apply Units.ext
  rw [val_wGL]
  show (wGLRat M ε h : Matrix (Fin 2) (Fin 2) ℚ).map (Rat.castHom ℝ) = _
  unfold wGLRat
  ext i j; fin_cases i <;> fin_cases j <;> simp

lemma isCusp_smul_of_rat {c : OnePoint ℝ} (hc : IsCusp c 𝒮ℒ) {g : GL (Fin 2) ℝ}
    (gQ : GL (Fin 2) ℚ) (hg : gQ.map (Rat.castHom ℝ) = g) : IsCusp (g • c) 𝒮ℒ := by
  subst hg
  rw [isCusp_SL2Z_iff] at hc ⊢
  obtain ⟨c₀, rfl⟩ := hc
  exact ⟨gQ • c₀, by rw [← Rat.coe_castHom, OnePoint.map_smul]⟩

def conjW (M : ℕ) [NeZero M] (ε : ℝ) (hε : ε = 1 ∨ ε = -1) {k : ℤ} (f : CuspForm Γ₁(M) k) :
    CuspForm Γ₁(M) k :=
  have hε0 : ε ≠ 0 := by rcases hε with rfl | rfl <;> norm_num
  { toFun := (⇑f : ℍ → ℂ) ∣[k] wGL M (NeZero.ne M) ε hε0
    slash_action_eq' := by
      intro A hA
      obtain ⟨γ, hγ, rfl⟩ := hA
      obtain ⟨γ', hγ', hcoc⟩ := exists_cocycle_wGL M (NeZero.ne M) ε hε0 hγ
      rw [← SlashAction.slash_mul, hcoc, SlashAction.slash_mul,
        SlashInvariantFormClass.slash_action_eq f _ (Subgroup.mem_map_of_mem _ hγ')]
    holo' := f.holo'.slash k _
    zero_at_cusps' := by
      intro c hc
      refine OnePoint.IsZeroAt.smul_iff.mp (CuspFormClass.zero_at_cusps f ?_)
      rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc ⊢
      have hMQ : (M : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne M
      rcases hε with rfl | rfl
      · have hQ : ((1 : ℤ) : ℚ) * ((1 : ℤ) : ℚ) * M ≠ 0 := by simpa using NeZero.ne M
        convert isCusp_smul_of_rat hc (wGLRat M 1 hQ) (wGLRat_map M (NeZero.ne M) 1 (by norm_num) hQ)
          using 2
        congr 1; norm_num
      · have hQ : ((-1 : ℤ) : ℚ) * ((-1 : ℤ) : ℚ) * M ≠ 0 := by simpa using NeZero.ne M
        convert isCusp_smul_of_rat hc (wGLRat M (-1) hQ)
          (wGLRat_map M (NeZero.ne M) (-1) (by norm_num) hQ) using 2
        congr 1; norm_num }

lemma coe_conjW (M : ℕ) [NeZero M] (ε : ℝ) (hε : ε = 1 ∨ ε = -1) {k : ℤ} (f : CuspForm Γ₁(M) k)
    (hε0 : ε ≠ 0) :
    (⇑(conjW M ε hε f) : ℍ → ℂ) = (⇑f : ℍ → ℂ) ∣[k] wGL M (NeZero.ne M) ε hε0 := rfl

lemma Gamma_le_Gamma1 (N : ℕ) : Gamma N ≤ Gamma1 N := by
  intro γ hγ
  rw [Gamma_mem] at hγ
  rw [Gamma1_mem]
  exact ⟨hγ.1, hγ.2.2.2, hγ.2.2.1⟩

def restrictΓ (N : ℕ) {k : ℤ} (f : CuspForm Γ₁(N) k) : CuspForm 𝒢(N) k where
  toFun := ⇑f
  slash_action_eq' γ hγ :=
    SlashInvariantFormClass.slash_action_eq f γ (Subgroup.map_mono (Gamma_le_Gamma1 N) hγ)
  holo' := CuspFormClass.holo f
  zero_at_cusps' hc := CuspFormClass.zero_at_cusps f (hc.mono (Subgroup.map_mono (Gamma_le_Gamma1 N)))

@[scoped simp] lemma coe_restrictΓ (N : ℕ) {k : ℤ} (f : CuspForm Γ₁(N) k) : ⇑(restrictΓ N f) = ⇑f := rfl

def ofInvariant (N M : ℕ) [NeZero N] [NeZero M] {k : ℤ} (G : CuspForm 𝒢(N) k)
    (hG : ∀ γ ∈ Gamma1 M, (⇑G : ℍ → ℂ) ∣[k] γ = ⇑G) : CuspForm Γ₁(M) k where
  toFun := ⇑G
  slash_action_eq' A hA := by
    obtain ⟨γ, hγ, rfl⟩ := hA
    exact hG γ hγ
  holo' := CuspFormClass.holo G
  zero_at_cusps' {c} hc := by
    refine CuspFormClass.zero_at_cusps G ?_
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc ⊢
    exact hc

@[scoped simp] lemma coe_ofInvariant (N M : ℕ) [NeZero N] [NeZero M] {k : ℤ} (G : CuspForm 𝒢(N) k)
    (hG : ∀ γ ∈ Gamma1 M, (⇑G : ℍ → ℂ) ∣[k] γ = ⇑G) : ⇑(ofInvariant N M G hG) = ⇑G := rfl

def slashV (N : ℕ) [NeZero N] {k : ℤ} (γ : SL(2, ℤ)) (G : CuspForm 𝒢(N) k) : CuspForm 𝒢(N) k where
  toFun := (⇑G : ℍ → ℂ) ∣[k] γ
  slash_action_eq' A hA := by
    obtain ⟨δ, hδ, rfl⟩ := hA
    have hδ' : γ * δ * γ⁻¹ ∈ Gamma N := (Gamma_normal N).conj_mem δ hδ γ
    have h1 : (⇑G : ℍ → ℂ) ∣[k] (γ * δ * γ⁻¹) = ⇑G :=
      SlashInvariantFormClass.slash_action_eq G _ (Subgroup.mem_map_of_mem _ hδ')
    calc ((⇑G : ℍ → ℂ) ∣[k] γ) ∣[k] mapGL ℝ δ
        = ((⇑G : ℍ → ℂ) ∣[k] γ) ∣[k] δ := rfl
      _ = (⇑G : ℍ → ℂ) ∣[k] (γ * δ) := by rw [SlashAction.slash_mul]
      _ = (⇑G : ℍ → ℂ) ∣[k] ((γ * δ * γ⁻¹) * γ) := by group
      _ = ((⇑G : ℍ → ℂ) ∣[k] (γ * δ * γ⁻¹)) ∣[k] γ := by rw [SlashAction.slash_mul]
      _ = (⇑G : ℍ → ℂ) ∣[k] γ := by rw [h1]
  holo' := (CuspFormClass.holo G).slash k _
  zero_at_cusps' {c} hc := by
    change IsZeroAt c ((⇑G : ℍ → ℂ) ∣[k] (mapGL ℝ γ)) k
    refine OnePoint.IsZeroAt.smul_iff.mp (CuspFormClass.zero_at_cusps G ?_)
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc ⊢
    exact hc.smul_of_mem ⟨γ, rfl⟩

@[scoped simp] lemma coe_slashV (N : ℕ) [NeZero N] {k : ℤ} (γ : SL(2, ℤ)) (G : CuspForm 𝒢(N) k) :
    ⇑(slashV N γ G) = (⇑G : ℍ → ℂ) ∣[k] γ := rfl

lemma slashV_of_mem (N : ℕ) [NeZero N] {k : ℤ} {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma N)
    (G : CuspForm 𝒢(N) k) : slashV N γ G = G := by
  refine CuspForm.ext fun τ => ?_
  rw [coe_slashV]
  exact congrFun (SlashInvariantFormClass.slash_action_eq G (mapGL ℝ γ)
    (Subgroup.mem_map_of_mem _ hγ)) τ

lemma slashV_mul (N : ℕ) [NeZero N] {k : ℤ} (γ δ : SL(2, ℤ)) (G : CuspForm 𝒢(N) k) :
    slashV N (γ * δ) G = slashV N δ (slashV N γ G) := by
  refine CuspForm.ext fun τ => ?_
  show ((⇑G : ℍ → ℂ) ∣[k] (γ * δ)) τ = (((⇑G : ℍ → ℂ) ∣[k] γ) ∣[k] δ) τ
  rw [SlashAction.slash_mul]

lemma slashV_add (N : ℕ) [NeZero N] {k : ℤ} (γ : SL(2, ℤ)) (G H : CuspForm 𝒢(N) k) :
    slashV N γ (G + H) = slashV N γ G + slashV N γ H := by
  refine CuspForm.ext fun τ => ?_
  show (((⇑G + ⇑H : ℍ → ℂ)) ∣[k] γ) τ = ((⇑G : ℍ → ℂ) ∣[k] γ) τ + ((⇑H : ℍ → ℂ) ∣[k] γ) τ
  rw [SlashAction.add_slash]; rfl

lemma slashV_smul (N : ℕ) [NeZero N] {k : ℤ} (γ : SL(2, ℤ)) (c : ℂ) (G : CuspForm 𝒢(N) k) :
    slashV N γ (c • G) = c • slashV N γ G := by
  refine CuspForm.ext fun τ => ?_
  show (((c • ⇑G : ℍ → ℂ)) ∣[k] γ) τ = c • ((⇑G : ℍ → ℂ) ∣[k] γ) τ
  rw [ModularForm.SL_smul_slash]; rfl

lemma slashV_sum (N : ℕ) [NeZero N] {k : ℤ} (γ : SL(2, ℤ)) {ι : Type*} (s : Finset ι)
    (G : ι → CuspForm 𝒢(N) k) :
    slashV N γ (∑ i ∈ s, G i) = ∑ i ∈ s, slashV N γ (G i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    refine CuspForm.ext fun τ => ?_
    show (((⇑(0 : CuspForm 𝒢(N) k)) : ℍ → ℂ) ∣[k] γ) τ = 0
    rw [FunLike.coe_zero, SlashAction.zero_slash]; rfl
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, slashV_add, ih]

lemma coe_eq_zero_of_qCoeff {L : ℕ} [NeZero L] {k : ℤ} (F : CuspForm Γ₁(L) k)
    (hF : ∀ n, ModularFormClass.qCoeff F n = 0) : (⇑F : ℍ → ℂ) = 0 := by
  funext τ
  have h := hasSum_qExp F τ
  have h0 : (fun n : ℕ => (qExpansion 1 ⇑F).coeff n • 𝕢 1 τ ^ n) = fun _ => 0 := by
    funext n
    have : (qExpansion 1 ⇑F).coeff n = 0 := hF n
    rw [this, zero_smul]
  rw [h0] at h
  exact h.unique hasSum_zero

section T1

variable {N : ℕ} [NeZero N] {k : ℤ}

def avgV (N : ℕ) [NeZero N] {k : ℤ} (p : ℕ) (D : CuspForm 𝒢(N) k) : CuspForm 𝒢(N) k :=
  (p : ℂ)⁻¹ • ∑ b ∈ Finset.range p, slashV N (lowU ((N / p : ℕ) : ℤ) ^ b) D

lemma coe_slashV_lowU_of_coe_eq (m : ℤ) (D : CuspForm 𝒢(N) k) (h : ℍ → ℂ)
    (hD : ⇑D = h ∣[k] W[N]) :
    ⇑(slashV N (lowU m) D) = (h ∣[k] transGL ((m : ℝ) / N)) ∣[k] W[N] := by
  rw [coe_slashV, hD]
  show (h ∣[k] W[N]) ∣[k] (mapGL ℝ (lowU m)) = _
  rw [← SlashAction.slash_mul, wGL_mul_lowU, SlashAction.slash_mul]

lemma coe_avgV_of_coe_eq {p : ℕ} (hp : p ≠ 0) (hpN : p ∣ N) (D : CuspForm 𝒢(N) k) (h : ℍ → ℂ)
    (hD : ⇑D = h ∣[k] W[N]) :
    ⇑(avgV N p D) = (fun τ => (p : ℂ)⁻¹ * ∑ b ∈ Finset.range p,
        h (((((b : ℤ) : ℝ) / p : ℝ)) +ᵥ τ)) ∣[k] W[N] := by
  have hNp : (N / p : ℕ) * p = N := Nat.div_mul_cancel hpN
  have key : ∀ b : ℕ, ⇑(slashV N (lowU ((N / p : ℕ) : ℤ) ^ b) D)
      = (fun τ => h (((((b : ℤ) : ℝ) / p : ℝ)) +ᵥ τ)) ∣[k] W[N] := by
    intro b
    rw [← lowU_natMul, coe_slashV_lowU_of_coe_eq _ D h hD]
    have hp' : (p : ℝ) ≠ 0 := by exact_mod_cast hp
    have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
    have hq : ((N / p : ℕ) : ℝ) * p = N := by exact_mod_cast hNp
    have e : (((((b : ℕ) : ℤ) * ((N / p : ℕ) : ℤ) : ℤ) : ℝ) / N) = (((b : ℕ) : ℤ) : ℝ) / p := by
      rw [Int.cast_mul, Int.cast_natCast, Int.cast_natCast, div_eq_div_iff hN' hp', mul_assoc, hq]
    congr 1
    funext τ
    rw [slash_transGL_apply, e]
  rw [avgV, FunLike.coe_smul, coe_finset_sum]
  simp_rw [key]
  rw [← sum_slash_wGL, ← smul_slash_wGL]
  congr 1
  funext τ
  rw [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]

lemma coe_sub_avgV {p : ℕ} (hp : p ≠ 0) (hpN : p ∣ N) {L : ℕ} [NeZero L]
    (h : CuspForm Γ₁(L) k) (D : CuspForm 𝒢(N) k) (hD : ⇑D = (⇑h : ℍ → ℂ) ∣[k] W[N]) :
    ⇑(D - avgV N p D) = (⇑(depleteForm h hp) : ℍ → ℂ) ∣[k] W[N] := by
  have hdep : (⇑(depleteForm h hp) : ℍ → ℂ)
      = (⇑h : ℍ → ℂ) - fun τ => (p : ℂ)⁻¹ * ∑ b ∈ Finset.range p,
          h (((((b : ℤ) : ℝ) / p : ℝ)) +ᵥ τ) := by
    funext τ; rw [depleteForm_apply]; rfl
  rw [hdep, sub_slash_wGL, FunLike.coe_sub, coe_avgV_of_coe_eq hp hpN D _ hD, hD]

lemma slashV_one (D : CuspForm 𝒢(N) k) : slashV N (1 : SL(2, ℤ)) D = D := by
  refine CuspForm.ext fun τ => ?_
  show ((⇑D : ℍ → ℂ) ∣[k] (1 : SL(2, ℤ))) τ = D τ
  rw [SlashAction.slash_one]

lemma slashV_lowU_avgV {p : ℕ} (hp : p ≠ 0) (hpN : p ∣ N) (D : CuspForm 𝒢(N) k) :
    slashV N (lowU ((N / p : ℕ) : ℤ)) (avgV N p D) = avgV N p D := by
  -- the frozen statement carries `hp : p ≠ 0` although the identity itself does not need it
  have _hp : p ≠ 0 := hp
  have hLp : slashV N (lowU ((N / p : ℕ) : ℤ) ^ p) D = D := by
    rw [← lowU_natMul]
    have h1 : ((p : ℤ) * ((N / p : ℕ) : ℤ)) = (N : ℤ) := by
      have h2 := Nat.div_mul_cancel hpN
      rw [mul_comm]; exact_mod_cast h2
    rw [h1]
    exact slashV_of_mem N (lowU_mem_Gamma N) D
  have h1 : ∀ b, slashV N (lowU ((N / p : ℕ) : ℤ)) (slashV N (lowU ((N / p : ℕ) : ℤ) ^ b) D)
      = slashV N (lowU ((N / p : ℕ) : ℤ) ^ (b + 1)) D := by
    intro b; rw [← slashV_mul, ← pow_succ]
  rw [avgV, slashV_smul, slashV_sum]
  congr 1
  simp_rw [h1]
  have e1 := Finset.sum_range_succ' (fun b => slashV N (lowU ((N / p : ℕ) : ℤ) ^ b) D) p
  have e2 := Finset.sum_range_succ (fun b => slashV N (lowU ((N / p : ℕ) : ℤ) ^ b) D) p
  have e3 := e1.symm.trans e2
  rw [pow_zero, slashV_one, hLp] at e3
  exact add_right_cancel e3

lemma exists_decomp (f : CuspForm Γ₁(N) k) (P : Finset ℕ) (hP : P ⊆ N.primeFactors) :
    ∃ (L : ℕ) (_ : NeZero L) (h : CuspForm Γ₁(L) k) (F : ℕ → CuspForm 𝒢(N) k)
      (D : CuspForm 𝒢(N) k),
      (∀ n, ModularFormClass.qCoeff h n =
        if (∀ p ∈ P, ¬ p ∣ n) then ModularFormClass.qCoeff f n else 0) ∧
      (⇑D = (⇑h : ℍ → ℂ) ∣[k] W[N]) ∧
      (∀ p ∈ P, slashV N (lowU ((N / p : ℕ) : ℤ)) (F p) = F p) ∧
      restrictΓ N (conjW N 1 (Or.inl rfl) f) = ∑ p ∈ P, F p + D := by
  classical
  induction P using Finset.induction_on with
  | empty =>
    refine ⟨N, inferInstance, f, fun _ => 0, restrictΓ N (conjW N 1 (Or.inl rfl) f),
      fun n => by simp, rfl, fun p hp => (Finset.notMem_empty p hp).elim, by simp⟩
  | insert p P hpP ih =>
    obtain ⟨L, hL, h, F, D, hh, hD, hF, hsum⟩ := ih ((Finset.subset_insert p P).trans hP)
    have hpmem : p ∈ N.primeFactors := hP (Finset.mem_insert_self p P)
    have hpr : p.Prime := Nat.prime_of_mem_primeFactors hpmem
    have hp0 : p ≠ 0 := hpr.ne_zero
    have hpN : p ∣ N := Nat.dvd_of_mem_primeFactors hpmem
    have : NeZero (L * p ^ 2) := ⟨mul_ne_zero (NeZero.ne L) (pow_ne_zero 2 hp0)⟩
    refine ⟨L * p ^ 2, inferInstance, depleteForm h hp0, Function.update F p (avgV N p D),
      D - avgV N p D, fun n => ?_, coe_sub_avgV hp0 hpN h D hD, fun q hq => ?_, ?_⟩
    · rw [qCoeff_depleteForm, hh n]
      by_cases h1 : p ∣ n
      · have h2 : ¬ (∀ p' ∈ insert p P, ¬ p' ∣ n) := fun h => h p (Finset.mem_insert_self _ _) h1
        rw [ite_eq_left h1, ite_eq_right h2]
      · rw [ite_eq_right h1]
        have h2 : (∀ p' ∈ P, ¬ p' ∣ n) ↔ (∀ p' ∈ insert p P, ¬ p' ∣ n) := by
          rw [Finset.forall_mem_insert]; exact ⟨fun h => ⟨h1, h⟩, fun h => h.2⟩
        exact if_congr h2 rfl rfl
    · rcases Finset.mem_insert.mp hq with rfl | hq'
      · rw [Function.update_self]; exact slashV_lowU_avgV hp0 hpN D
      · have hqp : q ≠ p := ne_of_mem_of_not_mem hq' hpP
        rw [Function.update_of_ne hqp]; exact hF q hq'
    · rw [Finset.sum_insert hpP, Function.update_self, hsum]
      have : ∑ x ∈ P, Function.update F p (avgV N p D) x = ∑ x ∈ P, F x := by
        refine Finset.sum_congr rfl fun x hx => ?_
        rw [Function.update_of_ne (ne_of_mem_of_not_mem hx hpP)]
      rw [this]; abel

lemma exists_pieces (f : CuspForm Γ₁(N) k)
    (hf : ∀ n : ℕ, n.Coprime N → ModularFormClass.qCoeff f n = 0) :
    ∃ F : ℕ → CuspForm 𝒢(N) k,
      (∀ p ∈ N.primeFactors, slashV N (lowU ((N / p : ℕ) : ℤ)) (F p) = F p) ∧
      restrictΓ N (conjW N 1 (Or.inl rfl) f) = ∑ p ∈ N.primeFactors, F p := by
  obtain ⟨L, hL, h, F, D, hh, hD, hF, hsum⟩ := exists_decomp f N.primeFactors subset_rfl
  refine ⟨F, hF, ?_⟩
  have hh0 : ∀ n, ModularFormClass.qCoeff h n = 0 := by
    intro n
    rw [hh n]
    split_ifs with h1
    · exact hf n ((coprime_iff_forall_primeFactors (NeZero.ne N) n).mpr h1)
    · rfl
  have hcoe : (⇑h : ℍ → ℂ) = 0 := coe_eq_zero_of_qCoeff h hh0
  have hD0 : D = 0 := by
    apply CuspForm.ext
    intro τ
    have := congrFun hD τ
    rw [hcoe, SlashAction.zero_slash] at this
    exact this
  rw [hsum, hD0, add_zero]

end T1

section T2

variable {N : ℕ} [NeZero N] {k : ℤ}

def pieceForm (N : ℕ) [NeZero N] {k : ℤ} (p : ℕ) (G : CuspForm 𝒢(N) k)
    (hG : p ∈ N.primeFactors → ∀ γ ∈ Gamma1 (N / p), (⇑G : ℍ → ℂ) ∣[k] γ = ⇑G) :
    CuspForm Γ₁(N / p) k :=
  if hp : p ∈ N.primeFactors then
    haveI : NeZero (N / p) := ⟨Nat.div_ne_zero_iff_of_dvd (Nat.dvd_of_mem_primeFactors hp)
      |>.mpr ⟨NeZero.ne N, (Nat.prime_of_mem_primeFactors hp).ne_zero⟩⟩
    (((N : ℂ) ^ (2 - k) * (p : ℂ) ^ (k - 1)) •
      conjW (N / p) (-1) (Or.inr rfl) (ofInvariant N (N / p) G (hG hp)))
  else 0

lemma pieceForm_apply {p : ℕ} (hp : p ∈ N.primeFactors) (G : CuspForm 𝒢(N) k)
    (hG : p ∈ N.primeFactors → ∀ γ ∈ Gamma1 (N / p), (⇑G : ℍ → ℂ) ∣[k] γ = ⇑G)
    (hNp : N / p ≠ 0) (τ : ℍ) :
    pieceForm N p G hG τ
      = ((N : ℂ) ^ (2 - k) * (p : ℂ) ^ (k - 1)) * ((⇑G : ℍ → ℂ) ∣[k] W'[N / p, hNp]) τ := by
  rw [pieceForm, dite_eq_left hp]
  rfl

lemma exists_forms (f : CuspForm Γ₁(N) k)
    (hf : ∀ n : ℕ, n.Coprime N → ModularFormClass.qCoeff f n = 0) :
    ∃ g : (p : ℕ) → CuspForm Γ₁(N / p) k,
      ∀ τ : ℍ, f τ = ∑ p ∈ N.primeFactors, g p (heckeDiagMatrix p • τ) := by
  obtain ⟨F, hF, hsum⟩ := exists_pieces f hf

  have hF' : ∀ p ∈ N.primeFactors, (⇑(F p) : ℍ → ℂ) ∣[k]
      (ModularGroup.S * ModularGroup.T ^ ((N / p : ℕ) : ℤ) * ModularGroup.S⁻¹) = ⇑(F p) := by
    intro p hp
    have := congrArg (fun G : CuspForm 𝒢(N) k => (⇑G : ℍ → ℂ)) (hF p hp)
    exact this
  have hsum' : ∀ γ ∈ Gamma1 N, (⇑(∑ p ∈ N.primeFactors, F p) : ℍ → ℂ) ∣[k] γ
      = ⇑(∑ p ∈ N.primeFactors, F p) := by
    intro γ hγ
    rw [← hsum]
    exact SlashInvariantFormClass.slash_action_eq (conjW N 1 (Or.inl rfl) f) (mapGL ℝ γ)
      (Subgroup.mem_map_of_mem _ hγ)
  obtain ⟨G, hG, hGsum⟩ :=
    CuspForm.exists_sum_eq_forall_gamma1_div_slash_eq N k F hF' hsum'
  refine ⟨fun p => pieceForm N p (G p) (fun hp => hG p hp), fun τ => ?_⟩

  have hfun : ∑ p ∈ N.primeFactors, (⇑(G p) : ℍ → ℂ) = (⇑f : ℍ → ℂ) ∣[k] W[N] := by
    rw [← coe_finset_sum, hGsum, ← hsum]; rfl

  have hN0 : N ≠ 0 := NeZero.ne N
  have h2 := congrArg (fun F : ℍ → ℂ => F ∣[k] W'[N, hN0]) hfun
  beta_reduce at h2
  rw [← SlashAction.slash_mul, wGL_mul_wGL N hN0, slash_scalar N hN0, sum_slash_wGL] at h2
  have h3 := congrFun h2 τ
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h3

  have hterm : ∀ p ∈ N.primeFactors, ((⇑(G p) : ℍ → ℂ) ∣[k] W'[N, hN0]) τ
      = (N : ℂ) ^ (k - 2) * pieceForm N p (G p) (fun hp => hG p hp) (heckeDiagMatrix p • τ) := by
    intro p hp
    have hpr : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hp0 : p ≠ 0 := hpr.ne_zero
    have hpN : p ∣ N := Nat.dvd_of_mem_primeFactors hp
    have hNp : N / p ≠ 0 := (Nat.div_ne_zero_iff_of_dvd hpN).mpr ⟨hN0, hp0⟩
    rw [wGL_eq_wGL_mul_heckeDiagMatrix hN0 hNp hp0 (Nat.div_mul_cancel hpN),
      SlashAction.slash_mul, slash_heckeDiagMatrix_apply k hp0, pieceForm_apply hp _ _ hNp]
    have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN0
    have hp' : (p : ℂ) ≠ 0 := by exact_mod_cast hp0
    have e1 : (N : ℂ) ^ (k - 2) * ((N : ℂ) ^ (2 - k) * (p : ℂ) ^ (k - 1)) = (p : ℂ) ^ (k - 1) := by
      rw [← mul_assoc, ← zpow_add₀ hN', show k - 2 + (2 - k) = 0 by ring, zpow_zero, one_mul]
    rw [← mul_assoc, e1]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum] at h3
  have hN' : (N : ℂ) ^ (k - 2) ≠ 0 := zpow_ne_zero _ (by exact_mod_cast hN0)
  exact mul_left_cancel₀ hN' h3.symm

theorem main (f : CuspForm Γ₁(N) k)
    (hf : ∀ n : ℕ, n.Coprime N → ModularFormClass.qCoeff f n = 0) :
    ∃ g : (p : ℕ) → CuspForm Γ₁(N / p) k,
      ∀ n : ℕ, ModularFormClass.qCoeff f n =
        ∑ p ∈ N.primeFactors, if p ∣ n then ModularFormClass.qCoeff (g p) (n / p) else 0 := by
  obtain ⟨g, hg⟩ := exists_forms f hf
  refine ⟨g, fun n => ?_⟩

  have hdeg : ∀ p ∈ N.primeFactors, ∃ Gd : CuspForm Γ₁(N) k,
      (∀ τ : ℍ, Gd τ = g p (heckeDiagMatrix p • τ)) ∧
      (∀ n : ℕ, ModularFormClass.qCoeff Gd n =
        if p ∣ n then ModularFormClass.qCoeff (g p) (n / p) else 0) := by
    intro p hp
    have hd : N / p * p ∣ N := by rw [Nat.div_mul_cancel (Nat.dvd_of_mem_primeFactors hp)]
    obtain ⟨Gd, h1, h2, -⟩ := CuspForm.exists_degeneracy_gamma1_hasNebentypus (k := k) hd (g p)
    exact ⟨Gd, h1, h2⟩
  choose Gd hGd1 hGd2 using hdeg
  have hfsum : ∀ τ : ℍ, f τ = ∑ q ∈ N.primeFactors.attach, Gd q.1 q.2 τ := by
    intro τ
    rw [hg τ, ← Finset.sum_attach N.primeFactors (fun p => (g p) (heckeDiagMatrix p • τ))]
    exact Finset.sum_congr rfl fun q _ => (hGd1 q.1 q.2 τ).symm
  have hHas : ∀ τ : ℍ, HasSum (fun m : ℕ =>
      (∑ q ∈ N.primeFactors.attach, (qExpansion 1 ⇑(Gd q.1 q.2)).coeff m) • 𝕢 1 τ ^ m)
      (f τ) := by
    intro τ
    rw [hfsum τ]
    have htr : ∀ q ∈ N.primeFactors.attach,
        HasSum (fun m : ℕ => (qExpansion 1 ⇑(Gd q.1 q.2)).coeff m • 𝕢 1 τ ^ m)
          (Gd q.1 q.2 τ) :=
      fun q _ => hasSum_qExp (Gd q.1 q.2) τ
    have := hasSum_sum htr
    simp_rw [Finset.sum_smul]
    exact this
  have huniq := ModularFormClass.qExpansion_coeff_unique one_pos
    (one_mem_strictPeriods_Gamma1 N) (f := f) hHas n
  show (qExpansion 1 ⇑f).coeff n = _
  rw [← huniq, ← Finset.sum_attach N.primeFactors
    (fun p => if p ∣ n then ModularFormClass.qCoeff (g p) (n / p) else 0)]
  exact Finset.sum_congr rfl fun q _ => hGd2 q.1 q.2 n

end T2

end AtkinLehnerMain

open CongruenceSubgroup
open scoped MatrixGroups

theorem CuspForm.exists_qCoeff_eq_sum_primeFactors_of_forall_coprime_qCoeff_eq_zero
    (N : ℕ) [NeZero N] (k : ℤ) (K : ℕ) (hK : K ≠ 0) (f : CuspForm (Gamma1 N) k)
    (hf : ∀ n : ℕ, Nat.Coprime n K → ModularFormClass.qCoeff f n = 0) :
    ∃ g : (p : ℕ) → CuspForm (Gamma1 (N / p)) k,
      ∀ n : ℕ, ModularFormClass.qCoeff f n =
        ∑ p ∈ N.primeFactors, if p ∣ n then ModularFormClass.qCoeff (g p) (n / p) else 0 :=
  AtkinLehnerMain.main f fun n hn =>
    CuspForm.qCoeff_eq_zero_of_coprime_level_of_forall_coprime_qCoeff_eq_zero N k K hK f hf n hn

end
