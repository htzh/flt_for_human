/-
  The Atkin–Lehner / diamond slash integrality
  (`P2M/Sol/S_ModularCurve_exists_isIntegralQExp_smul_atkinLehnerSlash_of_even.lean`,
  pin `aa2d8b3`), statement verbatim from
  `Theorems/Thm_ModularCurve_exists_isIntegralQExp_smul_atkinLehnerSlash_of_even.lean`.

  Slashing an integral `Γ₁(M) ⊓ Γ₀(Mℓ)`-form by `γ ∈ Γ₀(M)` with the diamond
  condition `ℓ ∣ γ 1 1` and pushing through `heckeDiagMatrix ℓ` keeps an integral
  `q`-expansion up to one global positive integer `D`. It is the `IsIntegralQExp`
  companion of the Γ₀-rationality pair (SET-R-A).

  Twenty of the pin `S_` file's 59 declarations are already public in the port and
  are **reused, not re-declared** (the `S_` file is in `SOURCES`, so they are matched
  by their existing homes):

  * the sixteen promoted `…X1DiamondRationalForms` rows of
    `ModularForms/WeightOne/Gamma0Integral.lean` (`IsRat`, `IsRat.mul`,
    `IsRat.pow`, `IsRat.of_mul_eq`, `isRat_iff_exists_map`, `isRat_E4`, `isRat_E6`,
    `isRat_Eaux`, `levelOne_smul`, `Eaux`, `qExpansion_Eaux`, `constantCoeff_E4`,
    `constantCoeff_E6`, `constantCoeff_Eaux`, `exists_weights`, `conj_mem_Gamma1`);
  * `ΓSL` (`ModularForms/WeightOne/RationalityDvd.lean`);
  * `disc_smul` (`ModularForms/WeightOne/Defs/GammaRational.lean`, `X1DiamondRational`);
  * `periodic_mul` (`ModularForms/DiscPow.lean`, `UpperHalfPlaneAux`);
  * `qExpansion_coeff_unique'` (`ModularForms/QExpansionCoeff.lean`).

  The remaining 38 declarations are newly transcribed here at their pin names,
  inside `ModularCurve.A2ALInt`, preserving the pin's section-variable spellings so
  the checker's textual diff sees the same statements. The pin's `p2m_reactivate`
  and the `attribute` lines of its wrapper are not transcribed.

  FLT provenance, pinned `aa2d8b3`:
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_exists_isIntegralQExp_smul_atkinLehnerSlash_of_even.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_exists_isIntegralQExp_smul_atkinLehnerSlash_of_even.lean
-/
import FLTForHuman.ModularForms.WeightOne.Gamma0Integral
import FLTForHuman.ModularForms.WeightOne.RationalityDvd
import FLTForHuman.ModularForms.QExpansionCoeff
import FLTForHuman.ModularForms.DiscPow
import FLTForHuman.ModularForms.Gamma1Vanishing
import FLTForHuman.ModularForms.HeckeQCoeff
import FLTForHuman.ModularCurve.X1.Defs
import FLTForHuman.ModularCurve.X1.Integral
import FLTForHuman.ModularCurve.JqIntegralRatios

set_option autoImplicit false
/- The pin's `haveI` walls are load-bearing; the style linter is suppressed rather
than replacing them with `have`. -/
set_option linter.style.haveILetI false

noncomputable section

open Complex UpperHalfPlane ModularForm CongruenceSubgroup Function ModularCurve
open scoped Real Manifold MatrixGroups ModularForm Topology Pointwise

namespace ModularCurve

namespace A2ALInt

open WLightS10.S_ModularCurve_exists_ratCast_qExpansion_slash_of_mem_Gamma0.X1DiamondRationalForms
open X1DiamondRational
open UpperHalfPlaneAux
open RatA

local notation "Δ" => ModularForm.discriminant

section Level

variable {M ℓ : ℕ} {k : ℤ}

abbrev Γ' (M ℓ : ℕ) : Subgroup (GL (Fin 2) ℝ) := ((ΓSL M ℓ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

theorem T_mem : ModularGroup.T ∈ ΓSL M ℓ := by
  refine Subgroup.mem_inf.mpr ⟨T_mem_Gamma1 M, ?_⟩
  rw [Gamma0_mem]
  simp [ModularGroup.T]

theorem one_mem_strictPeriods' : (1 : ℝ) ∈ (Γ' M ℓ).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem T_mem]
  exact AddSubgroup.mem_zmultiples _

scoped instance [NeZero M] [NeZero ℓ] : (ΓSL M ℓ).FiniteIndex := by
  haveI : NeZero (M * ℓ) := NeZero.mul
  refine Subgroup.finiteIndex_of_le (H := Gamma1 (M * ℓ)) (le_inf ?_ (Gamma1_in_Gamma0 _))
  exact ModularCurve.Gamma1_le_of_dvd (dvd_mul_right M ℓ)

def conjMat (ℓ : ℕ) (δ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![δ 0 0, (ℓ : ℤ) * δ 0 1; δ 1 0 / ℓ, δ 1 1]

theorem det_conjMat (δ : SL(2, ℤ)) (h : (ℓ : ℤ) ∣ δ 1 0) : (conjMat ℓ δ).det = 1 := by
  obtain ⟨c, hc⟩ := h
  have hdet := Matrix.SpecialLinearGroup.det_coe δ
  rw [Matrix.det_fin_two] at hdet ⊢
  rcases eq_or_ne (ℓ : ℤ) 0 with h0 | h0
  · simp only [conjMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, hc, h0, zero_mul, Int.zero_ediv,
      mul_zero, sub_zero] at hdet ⊢
    linear_combination hdet
  · have h1 : (ℓ : ℤ) * c / ℓ = c := by rw [mul_comm]; exact Int.mul_ediv_cancel c h0
    simp only [conjMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, hc, h1] at hdet ⊢
    linear_combination hdet

def conjSL (δ : SL(2, ℤ)) (h : (ℓ : ℤ) ∣ δ 1 0) : SL(2, ℤ) := ⟨conjMat ℓ δ, det_conjMat δ h⟩

@[scoped simp] theorem conjSL_apply_00 (δ : SL(2, ℤ)) (h : (ℓ : ℤ) ∣ δ 1 0) : conjSL δ h 0 0 = δ 0 0 := rfl
@[scoped simp] theorem conjSL_apply_01 (δ : SL(2, ℤ)) (h : (ℓ : ℤ) ∣ δ 1 0) :
    conjSL δ h 0 1 = (ℓ : ℤ) * δ 0 1 := rfl
@[scoped simp] theorem conjSL_apply_10 (δ : SL(2, ℤ)) (h : (ℓ : ℤ) ∣ δ 1 0) :
    conjSL δ h 1 0 = δ 1 0 / ℓ := rfl
@[scoped simp] theorem conjSL_apply_11 (δ : SL(2, ℤ)) (h : (ℓ : ℤ) ∣ δ 1 0) : conjSL δ h 1 1 = δ 1 1 := rfl

theorem dvd_of_mem_Gamma0_mul {δ : SL(2, ℤ)} (hδ : δ ∈ Gamma0 (M * ℓ)) : (ℓ : ℤ) ∣ δ 1 0 := by
  rw [Gamma0_mem] at hδ
  have : ((M * ℓ : ℕ) : ℤ) ∣ δ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hδ
  exact (show (ℓ : ℤ) ∣ ((M * ℓ : ℕ) : ℤ) from ⟨M, by push_cast; ring⟩).trans this

theorem conjSL_apply_10_eq {δ : SL(2, ℤ)} (hδ : δ ∈ Gamma0 (M * ℓ)) (hℓ : ℓ ≠ 0) :
    ∃ c : ℤ, (conjSL δ (dvd_of_mem_Gamma0_mul hδ)) 1 0 = M * c := by
  have hd : ((M * ℓ : ℕ) : ℤ) ∣ δ 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hδ)
  obtain ⟨c, hc⟩ := hd
  have hℓ' : (ℓ : ℤ) ≠ 0 := by exact_mod_cast hℓ
  refine ⟨c, ?_⟩
  show δ 1 0 / ℓ = M * c
  rw [hc]; push_cast
  rw [show (M : ℤ) * ℓ * c = ℓ * (M * c) by ring]
  exact Int.mul_ediv_cancel_left _ hℓ'

theorem conjSL_mem_Gamma1 {δ : SL(2, ℤ)} (hδ1 : δ ∈ Gamma1 M) (hδ : δ ∈ Gamma0 (M * ℓ)) (hℓ : ℓ ≠ 0) :
    conjSL δ (dvd_of_mem_Gamma0_mul hδ) ∈ Gamma1 M := by
  obtain ⟨c, hc⟩ := conjSL_apply_10_eq (M := M) hδ hℓ
  rw [Gamma1_mem] at hδ1 ⊢
  refine ⟨hδ1.1, hδ1.2.1, ?_⟩
  rw [hc]; push_cast; simp

theorem heckeDiag_mul_mul_inv {δ : SL(2, ℤ)} (h : (ℓ : ℤ) ∣ δ 1 0) (hℓ : ℓ ≠ 0) :
    ModularForm.heckeDiagMatrix ℓ * Matrix.SpecialLinearGroup.mapGL ℝ δ *
        (ModularForm.heckeDiagMatrix ℓ)⁻¹ =
      Matrix.SpecialLinearGroup.mapGL ℝ (conjSL δ h) := by
  rw [mul_inv_eq_iff_eq_mul]
  ext i j
  obtain ⟨c, hc⟩ := h
  have hℓ' : (ℓ : ℤ) ≠ 0 := by exact_mod_cast hℓ
  have h10 : (conjSL δ ⟨c, hc⟩ : SL(2, ℤ)) 1 0 = c := by
    show δ 1 0 / ℓ = c
    rw [hc]; exact Int.mul_ediv_cancel_left _ hℓ'
  simp only [Matrix.GeneralLinearGroup.coe_mul, ModularForm.val_heckeDiagMatrix hℓ]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, h10, hc] <;> ring

theorem conj_apply_10 (γ z : SL(2, ℤ)) :
    (γ * z * γ⁻¹) 1 0 = γ 1 0 * z 0 0 * γ 1 1 + γ 1 1 * z 1 0 * γ 1 1
      - γ 1 0 * z 0 1 * γ 1 0 - γ 1 1 * z 1 1 * γ 1 0 := by
  have hinv : (γ⁻¹ : SL(2, ℤ)) = ⟨!![γ 1 1, -(γ 0 1); -(γ 1 0), γ 0 0], by
      rw [Matrix.det_fin_two_of]; have := γ.det_coe; rw [Matrix.det_fin_two] at this
      linear_combination this⟩ := Matrix.SpecialLinearGroup.SL2_inv_expl γ
  rw [hinv]
  erw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

variable (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (hγℓ : (ℓ : ℤ) ∣ γ 1 1)

abbrev alGL (γ : SL(2, ℤ)) (ℓ : ℕ) : GL (Fin 2) ℝ :=
  Matrix.SpecialLinearGroup.mapGL ℝ γ * ModularForm.heckeDiagMatrix ℓ

include hγ hγℓ in

theorem alConj_mem {δ : SL(2, ℤ)} (hδ1 : δ ∈ Gamma1 M) (hδ : δ ∈ Gamma0 (M * ℓ))
    (hℓ : ℓ ≠ 0) : γ * conjSL δ (dvd_of_mem_Gamma0_mul hδ) * γ⁻¹ ∈ ΓSL M ℓ := by
  refine Subgroup.mem_inf.mpr ⟨conj_mem_Gamma1 hγ (conjSL_mem_Gamma1 hδ1 hδ hℓ), ?_⟩
  rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd, conj_apply_10]
  obtain ⟨r, hr⟩ : (M : ℤ) ∣ γ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hγ)
  obtain ⟨s, hs⟩ := hγℓ
  obtain ⟨c, hc⟩ := conjSL_apply_10_eq (M := M) hδ hℓ
  rw [hc, conjSL_apply_00, conjSL_apply_01, conjSL_apply_11, hr, hs]
  exact ⟨r * δ 0 0 * s + s * c * ℓ * s - r * δ 0 1 * M * r - s * δ 1 1 * r, by push_cast; ring⟩

include hγ hγℓ in

theorem le_conj_al (hℓ : ℓ ≠ 0) : Γ' M ℓ ≤ ConjAct.toConjAct (alGL γ ℓ)⁻¹ • Γ' M ℓ := by
  rintro x ⟨δ, hδ, rfl⟩
  obtain ⟨hδ1, hδ0⟩ := Subgroup.mem_inf.mp hδ
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, inv_inv,
    ConjAct.toConjAct_smul]
  refine ⟨_, alConj_mem γ hγ hγℓ hδ1 hδ0 hℓ, ?_⟩
  rw [map_mul, map_mul, map_inv, ← heckeDiag_mul_mul_inv (dvd_of_mem_Gamma0_mul hδ0) hℓ]
  simp only [alGL, _root_.mul_inv_rev, mul_assoc]

variable [NeZero ℓ]

def alForm (f : ModularForm (Γ' M ℓ) k) : ModularForm (Γ' M ℓ) k :=
  ((ℓ : ℂ) ^ (k - 1))⁻¹ •
    restrictForm (le_conj_al γ hγ hγℓ (NeZero.ne ℓ)) (ModularForm.translate f (alGL γ ℓ))

theorem alForm_apply (f : ModularForm (Γ' M ℓ) k) (τ : ℍ) :
    alForm γ hγ hγℓ f τ = (⇑f ∣[k] γ) (ModularForm.heckeDiagMatrix ℓ • τ) := by
  have hℓ : (ℓ : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne ℓ
  show ((ℓ : ℂ) ^ (k - 1))⁻¹ • ((⇑f ∣[k] alGL γ ℓ) τ) = _
  rw [alGL, SlashAction.slash_mul, ModularForm.slash_heckeDiagMatrix_apply k (NeZero.ne ℓ),
    smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ (zpow_ne_zero _ hℓ), one_mul]
  rfl

theorem coe_alForm (f : ModularForm (Γ' M ℓ) k) :
    ⇑(alForm γ hγ hγℓ f) = fun τ => (⇑f ∣[k] γ) (ModularForm.heckeDiagMatrix ℓ • τ) :=
  funext (alForm_apply γ hγ hγℓ f)

theorem le_conj_SL : Γ' M ℓ ≤ ConjAct.toConjAct (ModularForm.heckeDiagMatrix ℓ)⁻¹ • 𝒮ℒ := by
  rintro x ⟨δ, hδ, rfl⟩
  obtain ⟨-, hδ0⟩ := Subgroup.mem_inf.mp hδ
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, inv_inv,
    ConjAct.toConjAct_smul]
  exact ⟨_, (heckeDiag_mul_mul_inv (dvd_of_mem_Gamma0_mul hδ0) (NeZero.ne ℓ)).symm⟩

def levelRaise {kE : ℤ} (E : ModularForm 𝒮ℒ kE) : ModularForm (Γ' M ℓ) kE :=
  ((ℓ : ℂ) ^ (kE - 1))⁻¹ • restrictForm le_conj_SL (ModularForm.translate E (ModularForm.heckeDiagMatrix ℓ))

theorem levelRaise_apply {kE : ℤ} (E : ModularForm 𝒮ℒ kE) (τ : ℍ) :
    levelRaise (M := M) (ℓ := ℓ) E τ = E (ModularForm.heckeDiagMatrix ℓ • τ) := by
  have hℓ : (ℓ : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne ℓ
  show ((ℓ : ℂ) ^ (kE - 1))⁻¹ • ((⇑E ∣[kE] ModularForm.heckeDiagMatrix ℓ) τ) = _
  rw [ModularForm.slash_heckeDiagMatrix_apply kE (NeZero.ne ℓ), smul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ (zpow_ne_zero _ hℓ), one_mul]

theorem coeff_qExpansion_levelRaise {kE : ℤ} (E : ModularForm 𝒮ℒ kE) (n : ℕ) :
    (qExpansion 1 (levelRaise (M := M) (ℓ := ℓ) E)).coeff n =
      if ℓ ∣ n then (qExpansion 1 E).coeff (n / ℓ) else 0 := by
  have hcoe : (⇑(levelRaise (M := M) (ℓ := ℓ) E) : ℍ → ℂ) = fun τ => E (ModularForm.heckeDiagMatrix ℓ • τ) :=
    funext (levelRaise_apply E)
  rw [hcoe]
  exact ModularFormClass.qCoeff_comp_heckeDiagMatrix_smul E one_mem_strictPeriods_SL (NeZero.ne ℓ) n

theorem isRat_levelRaise {kE : ℤ} (E : ModularForm 𝒮ℒ kE) (hE : IsRat (qExpansion 1 E)) :
    IsRat (qExpansion 1 (levelRaise (M := M) (ℓ := ℓ) E)) := by
  intro n
  rw [coeff_qExpansion_levelRaise]
  split_ifs
  · exact hE _
  · exact ⟨0, by simp⟩

theorem constantCoeff_levelRaise {kE : ℤ} (E : ModularForm 𝒮ℒ kE)
    (hE : PowerSeries.constantCoeff (qExpansion 1 (E : ℍ → ℂ)) = 1) :
    PowerSeries.constantCoeff (qExpansion 1 (levelRaise (M := M) (ℓ := ℓ) E : ℍ → ℂ)) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_qExpansion_levelRaise, ite_eq_left (dvd_zero ℓ),
    Nat.zero_div, PowerSeries.coeff_zero_eq_constantCoeff_apply, hE]

omit [NeZero ℓ] in
include hγ in
theorem conj_T_pow_mem : γ * ModularGroup.T ^ (ℓ : ℤ) * γ⁻¹ ∈ ΓSL M ℓ := by
  have hc : (M : ℤ) ∣ γ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hγ)
  obtain ⟨r, hr⟩ := hc
  have hdet : (γ 0 0 : ℤ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.det_coe; rwa [Matrix.det_fin_two] at this
  have hinv : (γ⁻¹ : SL(2, ℤ)) = ⟨!![γ 1 1, -(γ 0 1); -(γ 1 0), γ 0 0], by
      rw [Matrix.det_fin_two_of]; have := γ.det_coe; rw [Matrix.det_fin_two] at this
      linear_combination this⟩ := Matrix.SpecialLinearGroup.SL2_inv_expl γ
  have h00 : (γ * ModularGroup.T ^ (ℓ : ℤ) * γ⁻¹) 0 0 = 1 - γ 0 0 * γ 1 0 * ℓ := by
    rw [hinv]
    erw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T_zpow]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination hdet
  have h11 : (γ * ModularGroup.T ^ (ℓ : ℤ) * γ⁻¹) 1 1 = 1 + γ 0 0 * γ 1 0 * ℓ := by
    rw [hinv]
    erw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T_zpow]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination hdet
  have h10 : (γ * ModularGroup.T ^ (ℓ : ℤ) * γ⁻¹) 1 0 = -(γ 1 0 * γ 1 0 * ℓ) := by
    rw [hinv]
    erw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T_zpow]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
    ring
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [Gamma1_mem, h00, h11, h10, hr]
    push_cast
    simp
  · rw [Gamma0_mem, h10, hr, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact ⟨-(r * M * r), by push_cast; ring⟩

omit [NeZero ℓ] in
include hγ in

theorem natCast_mem_strictPeriods_conj :
    (ℓ : ℝ) ∈ (ConjAct.toConjAct (Matrix.SpecialLinearGroup.mapGL ℝ γ)⁻¹ • Γ' M ℓ).strictPeriods := by
  rw [Subgroup.mem_strictPeriods_iff, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv,
    inv_inv, ConjAct.toConjAct_smul]
  refine ⟨_, conj_T_pow_mem γ hγ, ?_⟩
  have hT : Matrix.SpecialLinearGroup.mapGL ℝ (ModularGroup.T ^ (ℓ : ℤ)) =
      Matrix.GeneralLinearGroup.upperRightHom (ℓ : ℝ) := by
    apply Units.ext
    ext i j
    rw [Matrix.SpecialLinearGroup.mapGL_coe_matrix, Matrix.SpecialLinearGroup.map_apply_coe,
      ModularGroup.coe_T_zpow]
    fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.upperRightHom_apply]
  rw [map_mul, map_mul, map_inv, hT]

omit [NeZero ℓ] in
include hγ in

theorem periodic_slash (f : ModularForm (Γ' M ℓ) k) :
    Periodic (((⇑f : ℍ → ℂ) ∣[k] γ) ∘ ofComplex) ℓ := by
  have := SlashInvariantFormClass.periodic_comp_ofComplex
    (SlashInvariantForm.translate f (Matrix.SpecialLinearGroup.mapGL ℝ γ))
    (natCast_mem_strictPeriods_conj (M := M) γ hγ)
  rwa [SlashInvariantForm.coe_translate] at this

theorem isBoundedAtImInfty_slash [NeZero M] (f : ModularForm (Γ' M ℓ) k) (α : SL(2, ℤ)) :
    IsBoundedAtImInfty ((⇑f : ℍ → ℂ) ∣[k] α) := by
  rw [ModularForm.SL_slash, ← OnePoint.isBoundedAt_infty_iff, ← OnePoint.IsBoundedAt.smul_iff]
  apply f.bdd_at_cusps'
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z]
  exact isCusp_SL2Z_iff'.mpr ⟨α, rfl⟩

end Level

section Weight

variable {M ℓ : ℕ} [NeZero M] [NeZero ℓ] {k : ℤ}

omit [NeZero M] [NeZero ℓ] in
theorem periodic_disc_natCast : Periodic ((Δ : ℍ → ℂ) ∘ ofComplex) (ℓ : ℂ) := by
  have := SlashInvariantFormClass.periodic_comp_ofComplex CuspForm.discriminant one_mem_strictPeriods_SL
  rw [CuspForm.coe_discriminant] at this
  simpa using this.nat_mul ℓ

omit [NeZero M] [NeZero ℓ] in
theorem periodic_levelOne_natCast {k' : ℤ} (E : ModularForm 𝒮ℒ k') : Periodic ((⇑E : ℍ → ℂ) ∘ ofComplex) (ℓ : ℂ) := by
  have := SlashInvariantFormClass.periodic_comp_ofComplex E one_mem_strictPeriods_SL
  simpa using this.nat_mul ℓ

theorem isRat_slash_mul (f : ModularForm (Γ' M ℓ) k) (m : ℕ) {kE : ℤ} (E : ModularForm 𝒮ℒ kE)
    (hkE : k + kE = 12 * m) (hf : IsRat (qExpansion 1 f)) (hE : IsRat (qExpansion 1 E))
    {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) (hγℓ : (ℓ : ℤ) ∣ γ 1 1) :
    ∀ n, ∃ r : ℚ, (qExpansion ℓ (((⇑f : ℍ → ℂ) ∣[k] γ) * ⇑E)).coeff n = (r : ℂ) := by

  set H : ℍ → ℂ := (⇑f : ℍ → ℂ) * ⇑E with hH
  set G : ℍ → ℂ := fun τ => H τ / (Δ τ) ^ m with hG
  have hΔ : ∀ τ : ℍ, (Δ τ) ^ m ≠ 0 := fun τ => pow_ne_zero _ (discriminant_ne_zero τ)
  have hGΔ : G * Δ ^ m = H := by
    funext τ; simp only [Pi.mul_apply, Pi.pow_apply, hG]; field_simp [hΔ τ]
  have hmdH : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) H := f.holo'.mul E.holo'
  have hmdΔ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (Δ : ℍ → ℂ) := by
    rw [← CuspForm.coe_discriminant]; exact CuspForm.discriminant.holo'
  have hmdG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G := by
    intro τ
    exact (hmdH τ).div ((hmdΔ τ).pow m) (hΔ τ)

  have hcw : ∀ α : SL(2, ℤ), (fun τ => G (α • τ)) * Δ ^ m = ((⇑f : ℍ → ℂ) ∣[k] α) * ⇑E := by
    intro α
    funext τ
    have hd : denom (α : GL (Fin 2) ℝ) τ ≠ 0 := denom_ne_zero _ τ
    simp only [Pi.mul_apply, Pi.pow_apply, hG, hH]
    rw [ModularForm.SL_slash_apply, disc_smul, levelOne_smul E, ModularGroup.sl_moeb]
    have hpow : (denom (α : GL (Fin 2) ℝ) τ ^ (12 : ℤ) * Δ τ) ^ m
        = denom (α : GL (Fin 2) ℝ) τ ^ (k + kE) * (Δ τ) ^ m := by
      rw [mul_pow, ← zpow_natCast, ← zpow_mul, hkE]
    rw [hpow, zpow_add₀ hd, zpow_neg]
    field_simp [hΔ τ, zpow_ne_zero k hd, zpow_ne_zero kE hd]

  have hinv : ∀ g ∈ ΓSL M ℓ, ∀ τ : ℍ, G (g • τ) = G τ := by
    intro g hg τ
    have h1 := congrFun (hcw g) τ
    simp only [Pi.mul_apply, Pi.pow_apply] at h1
    have h2 : ((⇑f : ℍ → ℂ) ∣[k] g) = ⇑f := by
      rw [ModularForm.SL_slash]
      exact SlashInvariantFormClass.slash_action_eq f _ (Subgroup.mem_map_of_mem _ hg)
    rw [h2] at h1
    have h3 : G τ * Δ τ ^ m = f τ * E τ := by
      have := congrFun hGΔ τ; (simp only [Pi.mul_apply, Pi.pow_apply] at this; exact this)
    exact mul_right_cancel₀ (hΔ τ) (h1.trans h3.symm)

  have hbd : ∀ α : SL(2, ℤ), IsBoundedAtImInfty ((fun τ => G (α • τ)) * Δ ^ m) := by
    intro α
    rw [hcw α]
    exact (isBoundedAtImInfty_slash f α).mul (ModularFormClass.bdd_at_infty E)

  have hrat : ∀ n, ∃ r : ℚ, (qExpansion 1 (G * Δ ^ m)).coeff n = (r : ℂ) := by
    rw [hGΔ, hH]
    have : qExpansion 1 ((⇑f : ℍ → ℂ) * ⇑E) =
        qExpansion 1 ⇑f * qExpansion 1 ⇑(restrictForm (Subgroup.map_le_range _ _) E : ModularForm (Γ' M ℓ) kE) := by
      rw [← ModularForm.qExpansion_mul_coe one_pos one_mem_strictPeriods' f
        (restrictForm (Subgroup.map_le_range _ _) E : ModularForm (Γ' M ℓ) kE)]
      rfl
    rw [this]
    exact hf.mul hE

  have key := ModularCurve.exists_ratCast_qExpansion_comp_smul_of_mem_Gamma0_of_dvd M ℓ m G hmdG hinv hbd
    hrat γ hγ hγℓ
  rw [hcw γ] at key
  exact key

end Weight

section Width

variable {M ℓ : ℕ} [NeZero M] [NeZero ℓ] {k : ℤ}

theorem qParam_heckeDiag_smul (τ : ℍ) :
    Periodic.qParam (ℓ : ℝ) ((ModularForm.heckeDiagMatrix ℓ • τ : ℍ) : ℂ) = Periodic.qParam 1 τ := by
  simp only [Periodic.qParam]
  rw [ModularForm.coe_heckeDiagMatrix_smul (NeZero.ne ℓ)]
  congr 1
  have : (ℓ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne ℓ)
  push_cast
  field_simp

theorem qExpansion_coeff_comp_heckeDiag {Φ Ψ : ℍ → ℂ} (hper : Periodic (Φ ∘ ofComplex) (ℓ : ℂ))
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) Φ) (hbd : IsBoundedAtImInfty Φ)
    (hΨ : ∀ τ, Ψ τ = Φ (ModularForm.heckeDiagMatrix ℓ • τ)) (hΨan : AnalyticAt ℂ (cuspFunction 1 Ψ) 0)
    (n : ℕ) : (qExpansion 1 Ψ).coeff n = (qExpansion ℓ Φ).coeff n := by
  have hℓpos : (0 : ℝ) < ℓ := Nat.cast_pos.mpr (NeZero.pos ℓ)
  have hper' : Periodic (Φ ∘ ofComplex) ((ℓ : ℝ) : ℂ) := by simpa using hper
  have hsum : ∀ τ : ℍ, HasSum (fun m => (qExpansion ℓ Φ).coeff m • Periodic.qParam 1 τ ^ m) (Ψ τ) := by
    intro τ
    have := hasSum_qExpansion hℓpos hper' hhol hbd (ModularForm.heckeDiagMatrix ℓ • τ)
    rw [qParam_heckeDiag_smul (ℓ := ℓ), ← hΨ] at this
    exact this
  exact (qExpansion_coeff_unique' one_pos hΨan hsum n).symm

theorem isRat_alForm (hk : Even k) (f : ModularForm (Γ' M ℓ) k) (hf : IsRat (qExpansion 1 f))
    (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (hγℓ : (ℓ : ℤ) ∣ γ 1 1) :
    IsRat (qExpansion 1 (alForm γ hγ hγℓ f)) := by
  obtain ⟨m, a, b, hw⟩ := exists_weights hk
  set E := Eaux a b with hEdef
  have key := isRat_slash_mul f m E (by exact_mod_cast hw) hf (isRat_Eaux a b) hγ hγℓ

  set Ψ := (alForm γ hγ hγℓ f).mul (levelRaise (M := M) (ℓ := ℓ) E) with hΨ
  have hΨapply : ∀ τ, (Ψ : ℍ → ℂ) τ = (((⇑f : ℍ → ℂ) ∣[k] γ) * ⇑E) (ModularForm.heckeDiagMatrix ℓ • τ) := by
    intro τ
    simp only [hΨ, ModularForm.coe_mul, Pi.mul_apply, alForm_apply, levelRaise_apply]
  have hper : Periodic ((((⇑f : ℍ → ℂ) ∣[k] γ) * ⇑E) ∘ ofComplex) (ℓ : ℂ) :=
    periodic_mul (periodic_slash γ hγ f) (periodic_levelOne_natCast E)
  have hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (((⇑f : ℍ → ℂ) ∣[k] γ) * ⇑E) :=
    (f.holo'.slash k _).mul E.holo'
  have hbd : IsBoundedAtImInfty (((⇑f : ℍ → ℂ) ∣[k] γ) * ⇑E) :=
    (isBoundedAtImInfty_slash f γ).mul (ModularFormClass.bdd_at_infty E)
  have hΨan : AnalyticAt ℂ (cuspFunction 1 (Ψ : ℍ → ℂ)) 0 :=
    ModularFormClass.analyticAt_cuspFunction_zero Ψ one_pos one_mem_strictPeriods'
  have hΨrat : IsRat (qExpansion 1 (Ψ : ℍ → ℂ)) := by
    intro n
    rw [qExpansion_coeff_comp_heckeDiag hper hhol hbd hΨapply hΨan n]
    exact key n
  have hprod : qExpansion 1 (Ψ : ℍ → ℂ) =
      qExpansion 1 (alForm γ hγ hγℓ f) * qExpansion 1 (levelRaise (M := M) (ℓ := ℓ) E) := by
    rw [hΨ, ModularForm.coe_mul, ModularForm.qExpansion_mul_coe one_pos one_mem_strictPeriods']
  exact IsRat.of_mul_eq (isRat_levelRaise E (isRat_Eaux a b))
    (constantCoeff_levelRaise E (constantCoeff_Eaux a b)) hΨrat hprod.symm

end Width

theorem cardK (M ℓ : ℕ) [NeZero M] [NeZero ℓ] {k : ℤ} (hk : Even k)
    (f : ModularForm (Γ' M ℓ) k) {p : PowerSeries ℤ} (hp : IsIntegralQExp f p)
    (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (hγℓ : (ℓ : ℤ) ∣ γ 1 1) :
    ∃ (D : ℤ) (p₁ : PowerSeries ℤ), D ≠ 0 ∧
      IsIntegralQExp ((D : ℂ) • fun τ : ℍ => ((⇑f : ℍ → ℂ) ∣[k] γ) (ModularForm.heckeDiagMatrix ℓ • τ)) p₁ := by
  haveI : NeZero (M * ℓ) := NeZero.mul

  have hf : IsRat (qExpansion 1 f) := fun n => ⟨((PowerSeries.coeff n p : ℤ) : ℚ), by
    rw [← hp.coeff n]; push_cast; rfl⟩
  have hrat := isRat_alForm hk f hf γ hγ hγℓ

  have hle : ((Gamma1 (M * ℓ) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤ Γ' M ℓ :=
    Subgroup.map_mono (le_inf (ModularCurve.Gamma1_le_of_dvd (dvd_mul_right M ℓ)) (Gamma1_in_Gamma0 _))
  obtain ⟨D, p₁, hD, hp₁⟩ := ModularCurve.exists_isIntegralQExp_smul_of_ratCast_qExpansion (M * ℓ)
    (restrictForm hle (alForm γ hγ hγℓ f)) hrat
  refine ⟨D, p₁, hD, ?_⟩
  rw [← coe_alForm γ hγ hγℓ f]
  exact hp₁

end A2ALInt

open scoped MatrixGroups ModularForm in
theorem exists_isIntegralQExp_smul_atkinLehnerSlash_of_even (M ℓ : ℕ) [NeZero M]
    [NeZero ℓ] {k : ℤ} (hk : Even k)
    (f : ModularForm ((CongruenceSubgroup.Gamma1 M ⊓ CongruenceSubgroup.Gamma0 (M * ℓ) :
      Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k)
    {p : PowerSeries ℤ} (hp : ModularCurve.IsIntegralQExp f p)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M) (hγℓ : (ℓ : ℤ) ∣ γ 1 1) :
    ∃ (D : ℤ) (p₁ : PowerSeries ℤ), D ≠ 0 ∧
      ModularCurve.IsIntegralQExp
        ((D : ℂ) • fun τ : UpperHalfPlane =>
          ((⇑f : UpperHalfPlane → ℂ) ∣[k] γ) (ModularForm.heckeDiagMatrix ℓ • τ)) p₁ :=
  A2ALInt.cardK M ℓ hk f hp γ hγ hγℓ

end ModularCurve
