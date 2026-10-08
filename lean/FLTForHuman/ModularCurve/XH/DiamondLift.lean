/-
The `X_H(M)` specialisation of the diamond-lift engine (`XH/DiamondLiftPrelude.lean`)
and the headline `ModularCurve.exists_algEquiv_intertwinesAlong_diamondAutHBar`.

This is the level-specific half of
`P2M/Sol/S_ModularCurve_exists_algEquiv_intertwinesAlong_diamondAutHBar.lean`
(pin `aa2d8b3`): the `Γ_H(M)`-level instances and cocycle, `rationalSlash_level`
for `Γ_H(M) ⊓ Γ₀(Mℓ)`, the `Genuine` block (`genH`/`witness`/`coeffEmb_injective'`/
`tau0_incl_generator`/`tau0_qExpand_generator`) and `main` over the base change
`ℚ̄`. Its sibling `X1/DiamondLift.lean` is the `Γ₁(M)` case.

https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_exists_algEquiv_intertwinesAlong_diamondAutHBar.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_exists_algEquiv_intertwinesAlong_diamondAutHBar.lean
-/
import FLTForHuman.ModularCurve.XH.DiamondLiftPrelude
import FLTForHuman.ModularCurve.XH.Operators
import FLTForHuman.ModularCurve.X1.BaseChangeCover
import FLTForHuman.ModularForms.Defs.GammaH

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 1600000
set_option linter.style.haveILetI false

noncomputable section

open UpperHalfPlane ModularForm CongruenceSubgroup OnePoint Function HahnSeries AlgebraicCurve
open scoped MatrixGroups ModularForm Manifold

namespace ModularCurve

namespace DiamondLift

namespace XH

local notation "GL↑(" Γ ")" => ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))
local notation "ℚbar" => AlgebraicClosure ℚ

/-! ## The `Γ_H(M) ⊓ Γ₀(Mℓ)` level -/

scoped instance isLevel_GammaH (M : ℕ) (H : Subgroup (ZMod M)ˣ) : IsLevel (CohCarrier.GammaH M H) :=
  ⟨CohCarrier.translation_mem_GammaH M H⟩

scoped instance isLevel_GammaH_inf_Gamma0 (M : ℕ) (H : Subgroup (ZMod M)ˣ) (t : ℕ) :
    IsLevel (CohCarrier.GammaH M H ⊓ Gamma0 t) :=
  ⟨⟨IsLevel.T_mem, Gamma0_mem.mpr (by simp [ModularGroup.T])⟩⟩

scoped instance normalizes_Gamma0_GammaH (M : ℕ) (H : Subgroup (ZMod M)ˣ) :
    Normalizes (Gamma0 M) (CohCarrier.GammaH M H) :=
  ⟨fun _ _ hγ hA => CohCarrier.conj_mem_GammaH M H ⟨_, hγ⟩ ⟨_, hA⟩⟩

scoped instance normalizes_level (M : ℕ) (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) :
    Normalizes (Gamma0 (M * ℓ)) (CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ)) :=
  ⟨fun _ _ hγ hA => ⟨CohCarrier.conj_mem_GammaH M H ⟨_, Gamma0_mul_le M ℓ hγ⟩ ⟨_, hA.1⟩,
    (Gamma0 (M * ℓ)).mul_mem ((Gamma0 (M * ℓ)).mul_mem hγ hA.2) ((Gamma0 (M * ℓ)).inv_mem hγ)⟩⟩

scoped instance finiteIndex_GammaH (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    (CohCarrier.GammaH M H).FiniteIndex :=
  Subgroup.finiteIndex_of_le (CohCarrier.Gamma1_le_GammaH M H)

scoped instance finiteIndex_level (M : ℕ) (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) [NeZero M] [NeZero ℓ] :
    (CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ)).FiniteIndex := by
  haveI := neZero_mul M ℓ
  infer_instance

theorem Gamma1_mul_le_level (M : ℕ) (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) :
    Gamma1 (M * ℓ) ≤ CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ) :=
  le_inf ((Gamma1_le_of_dvd (dvd_mul_right M ℓ)).trans (CohCarrier.Gamma1_le_GammaH M H)) (Gamma1_in_Gamma0 _)

theorem cocycle (M : ℕ) (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) [NeZero ℓ] :
    ∀ γ ∈ CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ), ∃ γ₁ ∈ CohCarrier.GammaH M H,
    γ₁ 0 0 = γ 0 0 ∧ γ₁ 0 1 = (ℓ : ℤ) * γ 0 1 ∧ (ℓ : ℤ) * γ₁ 1 0 = γ 1 0 ∧ γ₁ 1 1 = γ 1 1 := by
  intro γ hγ
  obtain ⟨hγH, hγ0⟩ := Subgroup.mem_inf.mp hγ
  obtain ⟨hγ0M, hunit⟩ := CohCarrier.mem_GammaH_iff.mp hγH
  have hdet : (γ 0 0 : ℤ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.det_coe; rwa [Matrix.det_fin_two] at this
  have hMℓc : ((M * ℓ : ℕ) : ℤ) ∣ γ 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hγ0)
  obtain ⟨c', hc'⟩ := hMℓc
  rw [Nat.cast_mul] at hc'
  have hdet' : Matrix.det !![(γ 0 0 : ℤ), (ℓ : ℤ) * γ 0 1; (M : ℤ) * c', γ 1 1] = 1 := by
    rw [Matrix.det_fin_two_of]; linear_combination hdet + (γ 0 1 : ℤ) * hc'
  -- v4.34 no longer elaborates the bare `⟨_, hdet'⟩` against `SL(2, ℤ)` inside
  -- `mem_GammaH_iff`'s argument; naming the witness first is the port's idiom
  -- (`CohCarrier.gamma0Units_surjective`).
  let γ₁ : SL(2, ℤ) := ⟨!![(γ 0 0 : ℤ), (ℓ : ℤ) * γ 0 1; (M : ℤ) * c', γ 1 1], hdet'⟩
  have h0 : γ₁ ∈ Gamma0 M := by
    rw [Gamma0_mem]
    show (((M : ℤ) * c' : ℤ) : ZMod M) = 0
    push_cast; rw [ZMod.natCast_self, zero_mul]
  have h1 : γ₁ ∈ CohCarrier.GammaH M H := by
    rw [CohCarrier.mem_GammaH_iff]
    refine ⟨h0, ?_⟩
    have hu : CohCarrier.gamma0Units M ⟨γ₁, h0⟩ = CohCarrier.gamma0Units M ⟨γ, hγ0M⟩ := by
      refine Units.ext ?_
      simp only [CohCarrier.gamma0Units, MonoidHom.coe_mk, OneHom.coe_mk, Gamma0Map]
      simp [γ₁]
    rw [hu]
    exact hunit
  refine ⟨γ₁, h1, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · show (ℓ : ℤ) * ((M : ℤ) * c') = γ 1 0
    linear_combination -hc'
  · rfl

theorem rationalSlash_level (M : ℕ) (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) [NeZero M] [NeZero ℓ] :
    RationalSlash (CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ)) (Gamma0 (M * ℓ)) := by
  intro k f p hp γ hγ
  haveI := neZero_mul M ℓ
  have hle : Gamma1 (M * ℓ) ≤ CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ) := Gamma1_mul_le_level M H ℓ
  have hle' : GL↑(Gamma1 (M * ℓ)) ≤ GL↑(CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ)) := Subgroup.map_mono hle
  obtain ⟨D, f₁, p₁, hD, hp₁, hf₁⟩ :=
    ModularCurve.exists_isIntegralQExp_smul_slash_of_mem_Gamma0 (M * ℓ) (restrictForm hle' f)
      (by rw [IsIntegralQExp, coe_restrictForm]; exact hp) γ hγ
  refine ⟨D, (D : ℂ) • slashForm γ hγ f, p₁, hD, ?_, ?_⟩
  · have : (⇑((D : ℂ) • slashForm γ hγ f) : ℍ → ℂ) = ⇑f₁ := by
      rw [FunLike.coe_smul, coe_slashForm_SL, hf₁, coe_restrictForm]
    rw [IsIntegralQExp, this]
    exact hp₁
  · rw [FunLike.coe_smul, coe_slashForm_SL]

abbrev FB (M : ℕ) (H : Subgroup (ZMod M)ˣ) : IntermediateField ℚ (LaurentSeries ℚ) :=
  qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)

abbrev FT (M : ℕ) (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) : IntermediateField ℚ (LaurentSeries ℚ) :=
  qExpFunctionFieldC ℚ (CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ))

theorem FB_le_FT (M : ℕ) (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) : FB M H ≤ FT M H ℓ :=
  qExpFunctionFieldC_mono ℚ inf_le_left

/-! ## The genuine diamond lift on `Γ_H(M)` -/

section Genuine

variable {M ℓ : ℕ} [NeZero M] [NeZero ℓ] {H : Subgroup (ZMod M)ˣ} {d : (ZMod M)ˣ}
  {σd : xHFunctionFieldBar M H ≃ₐ[ℚbar] xHFunctionFieldBar M H} (hσd : IsDiamondAutHBar M H d σd)
  {γ γ' : SL(2, ℤ)} (hγ : γ ∈ Gamma0 (M * ℓ)) (hγ' : γ' ∈ Gamma0 M)
  (hγd : ((γ 0 0 : ℤ) : ZMod M) = (d : ZMod M)) (hγ'd : ((γ' 0 0 : ℤ) : ZMod M) = (d : ZMod M))
  (hc : heckeDiagMatrix ℓ * Matrix.SpecialLinearGroup.mapGL ℝ γ
    = Matrix.SpecialLinearGroup.mapGL ℝ γ' * heckeDiagMatrix ℓ)

/-- The `Γ_H(M)`-generator `f/g` pushed to `X_H(M)` over `ℚ̄`. -/
def genH {k : ℤ} (f g : ModularForm GL↑(CohCarrier.GammaH M H) k) {pf pg : PowerSeries ℤ}
    (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0) :
    xHFunctionFieldBar M H :=
  ⟨coeffEmb ℚbar (intSeriesC ℚ pf / intSeriesC ℚ pg),
    coeffEmb_mem_laurentBaseChange ℚbar (div_mem_qExpFunctionFieldC f g hf hg hg0)⟩

include hσd in

theorem witness {γ₀ : SL(2, ℤ)} (hγ₀ : γ₀ ∈ Gamma0 M) (hγ₀d : ((γ₀ 0 0 : ℤ) : ZMod M) = (d : ZMod M))
    {k : ℤ} (f g : ModularForm GL↑(CohCarrier.GammaH M H) k) {pf pg : PowerSeries ℤ}
    (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0) :
    ∃ y : LaurentSeries ℚ, y ∈ FB M H ∧
      ((σd (genH f g hf hg hg0) : xHFunctionFieldBar M H) : LaurentSeries ℚbar) = coeffEmb ℚbar y ∧
      toC y = qC ((⇑f : ℍ → ℂ) ∣[k] γ₀) / qC ((⇑g : ℍ → ℂ) ∣[k] γ₀) := by
  obtain ⟨y, hyF, hy, hrel⟩ := hσd k f g pf pg hf hg hg0 γ₀ hγ₀ hγ₀d
  refine ⟨y, hyF, hy, ?_⟩
  rw [eq_div_iff (qC_slash_ne_zero (Γ := CohCarrier.GammaH M H) γ₀ hγ₀
    (qC_ne_zero_of_intSeriesC_ne_zero hg hg0))]
  exact hrel

theorem coeffEmb_injective' : Function.Injective (coeffEmb ℚbar) := by
  intro x y h
  ext n
  have := congrArg (fun z : LaurentSeries ℚbar => z.coeff n) h
  simp only [coeffEmb_coeff] at this
  exact (algebraMap ℚ ℚbar).injective this

include hσd hγd in

theorem tau0_incl_generator {k : ℤ} (f g : ModularForm GL↑(CohCarrier.GammaH M H) k)
    {pf pg : PowerSeries ℤ} (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg)
    (hg0 : intSeriesC ℚ pg ≠ 0) {y : LaurentSeries ℚ}
    (hy : ((σd (genH f g hf hg hg0) : xHFunctionFieldBar M H) : LaurentSeries ℚbar) = coeffEmb ℚbar y) :
    ((sigma (rationalSlash_level M H ℓ) γ hγ
        ⟨intSeriesC ℚ pf / intSeriesC ℚ pg, FB_le_FT M H ℓ (div_mem_qExpFunctionFieldC f g hf hg hg0)⟩ :
          FT M H ℓ) : LaurentSeries ℚ) = y := by
  obtain ⟨y', -, hy', hrel'⟩ := witness hσd (Gamma0_mul_le M ℓ hγ) hγd f g hf hg hg0
  have hyy : y = y' := coeffEmb_injective' (hy.symm.trans hy')
  apply toC_injective
  have hle' : GL↑(CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ)) ≤ GL↑(CohCarrier.GammaH M H) :=
    Subgroup.map_mono inf_le_left
  have hf' : IsIntegralQExp (restrictForm hle' f) pf := by
    rw [IsIntegralQExp, coe_restrictForm]; exact hf
  have hg' : IsIntegralQExp (restrictForm hle' g) pg := by
    rw [IsIntegralQExp, coe_restrictForm]; exact hg
  have h1 := toC_sigma_generator (rationalSlash_level M H ℓ) γ hγ (restrictForm hle' f)
    (restrictForm hle' g) hf' hg' hg0
  rw [coe_restrictForm, coe_restrictForm] at h1
  rw [hyy, hrel']
  exact h1

include hσd hγ' hγ'd hc in

theorem tau0_qExpand_generator {k : ℤ} (f g : ModularForm GL↑(CohCarrier.GammaH M H) k)
    {pf pg : PowerSeries ℤ} (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg)
    (hg0 : intSeriesC ℚ pg ≠ 0)
    (hmem : qExpand ℚ ℓ (intSeriesC ℚ pf / intSeriesC ℚ pg) ∈ FT M H ℓ) {y : LaurentSeries ℚ}
    (hy : ((σd (genH f g hf hg hg0) : xHFunctionFieldBar M H) : LaurentSeries ℚbar) = coeffEmb ℚbar y) :
    ((sigma (rationalSlash_level M H ℓ) γ hγ ⟨qExpand ℚ ℓ (intSeriesC ℚ pf / intSeriesC ℚ pg), hmem⟩ :
          FT M H ℓ) : LaurentSeries ℚ) = qExpand ℚ ℓ y := by
  have hℓ : ℓ ≠ 0 := NeZero.ne ℓ
  obtain ⟨y', -, hy', hrel'⟩ := witness hσd hγ' hγ'd f g hf hg hg0
  have hyy : y = y' := coeffEmb_injective' (hy.symm.trans hy')
  apply toC_injective
  have hSf : IsIntegralQExp (stretch (Γ' := CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ)) (cocycle M H ℓ) hℓ f)
      (expandPS ℓ pf) := isIntegralQExp_stretch _ hℓ f hf
  have hSg : IsIntegralQExp (stretch (Γ' := CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ)) (cocycle M H ℓ) hℓ g)
      (expandPS ℓ pg) := isIntegralQExp_stretch _ hℓ g hg
  have hSg0 : intSeriesC ℚ (expandPS ℓ pg) ≠ 0 := by
    rw [intSeriesC_expandPS]
    exact fun h => hg0 (ModularCurve.qExpand_injective ℓ (by rw [h, map_zero]))
  have hx : (⟨qExpand ℚ ℓ (intSeriesC ℚ pf / intSeriesC ℚ pg), hmem⟩ : FT M H ℓ)
      = ⟨intSeriesC ℚ (expandPS ℓ pf) / intSeriesC ℚ (expandPS ℓ pg),
          div_mem_qExpFunctionFieldC _ _ hSf hSg hSg0⟩ := by
    apply Subtype.ext
    show qExpand ℚ ℓ (intSeriesC ℚ pf / intSeriesC ℚ pg)
      = intSeriesC ℚ (expandPS ℓ pf) / intSeriesC ℚ (expandPS ℓ pg)
    rw [map_div₀, intSeriesC_expandPS, intSeriesC_expandPS]
  rw [hx, toC_sigma_generator (rationalSlash_level M H ℓ) γ hγ _ _ hSf hSg hSg0]
  rw [stretch_slash (cocycle M H ℓ) hℓ f hγ' hc, stretch_slash (cocycle M H ℓ) hℓ g hγ' hc,
    qC_stretch, qC_stretch, ← map_div₀, coe_slashForm_SL, coe_slashForm_SL, ← hrel', toC_qExpand, hyy]

end Genuine

/-! ## The base change to `ℚ̄` and the headline -/

theorem laurentBaseChange_eq_adjoin_ratios (M : ℕ) (H : Subgroup (ZMod M)ˣ) :
    laurentBaseChange ℚbar (FB M H)
      = IntermediateField.adjoin ℚbar (⇑(coeffEmb ℚbar) '' intFormRatiosC ℚ (CohCarrier.GammaH M H)) := by
  apply le_antisymm
  · rw [laurentBaseChange, IntermediateField.adjoin_le_iff]
    rintro _ ⟨y, hy, rfl⟩
    show coeffEmb ℚbar y ∈ IntermediateField.adjoin ℚbar (⇑(coeffEmb ℚbar) '' intFormRatiosC ℚ (CohCarrier.GammaH M H))
    have hy' : y ∈ IntermediateField.adjoin ℚ (intFormRatiosC ℚ (CohCarrier.GammaH M H)) := hy
    clear hy
    induction hy' using IntermediateField.adjoin_induction with
    | mem x hx => exact IntermediateField.subset_adjoin ℚbar _ ⟨x, hx, rfl⟩
    | algebraMap r =>
        rw [eq_ratCast, map_ratCast]
        exact SubfieldClass.ratCast_mem _ r
    | add x x' _ _ ihx ihx' => rw [map_add]; exact add_mem ihx ihx'
    | inv x _ ihx => rw [map_inv₀]; exact inv_mem ihx
    | mul x x' _ _ ihx ihx' => rw [map_mul]; exact mul_mem ihx ihx'
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨x, hx, rfl⟩
    exact coeffEmb_mem_laurentBaseChange ℚbar (intFormRatiosC_subset ℚ _ hx)

section Main

variable (M ℓ : ℕ) [NeZero M] [NeZero ℓ] (H : Subgroup (ZMod M)ˣ) (d : (ZMod M)ˣ)
  {σd : xHFunctionFieldBar M H ≃ₐ[ℚbar] xHFunctionFieldBar M H} (hσd : IsDiamondAutHBar M H d σd)
  {γ γ' : SL(2, ℤ)} (hγ : γ ∈ Gamma0 (M * ℓ)) (hγ' : γ' ∈ Gamma0 M)
  (hγd : ((γ 0 0 : ℤ) : ZMod M) = (d : ZMod M)) (hγ'd : ((γ' 0 0 : ℤ) : ZMod M) = (d : ZMod M))
  (hc : heckeDiagMatrix ℓ * Matrix.SpecialLinearGroup.mapGL ℝ γ
    = Matrix.SpecialLinearGroup.mapGL ℝ γ' * heckeDiagMatrix ℓ)
  (τ : laurentBaseChange ℚbar (FT M H ℓ) ≃ₐ[ℚbar] laurentBaseChange ℚbar (FT M H ℓ))
  (hτ : ∀ y : FT M H ℓ,
    ((τ ⟨coeffEmb ℚbar (y : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange ℚbar y.2⟩ :
        laurentBaseChange ℚbar (FT M H ℓ)) : LaurentSeries ℚbar)
      = coeffEmb ℚbar ((sigma (rationalSlash_level M H ℓ) γ hγ y : FT M H ℓ) : LaurentSeries ℚ))

include hσd hγd hτ in

theorem comp_alpha_eq :
    (τ : laurentBaseChange ℚbar (FT M H ℓ) →ₐ[ℚbar] laurentBaseChange ℚbar (FT M H ℓ)).comp
        (heckeAlphaHBar ℚbar M H ℓ)
      = (heckeAlphaHBar ℚbar M H ℓ).comp
          (σd : xHFunctionFieldBar M H →ₐ[ℚbar] xHFunctionFieldBar M H) := by
  refine IntermediateField.algHom_ext_of_eq_adjoin (F := ℚbar)
    (s := ⇑(coeffEmb ℚbar) '' intFormRatiosC ℚ (CohCarrier.GammaH M H))
    (laurentBaseChange_eq_adjoin_ratios M H) ?_
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ := hx
  obtain ⟨y, hyF, hy, -⟩ := witness hσd (Gamma0_mul_le M ℓ hγ) hγd f g hf hg hg0
  apply Subtype.ext
  show ((τ (heckeAlphaHBar ℚbar M H ℓ (genH f g hf hg hg0)) : laurentBaseChange ℚbar (FT M H ℓ)) :
      LaurentSeries ℚbar)
    = ((heckeAlphaHBar ℚbar M H ℓ (σd (genH f g hf hg hg0)) : laurentBaseChange ℚbar (FT M H ℓ)) :
      LaurentSeries ℚbar)
  have e1 : heckeAlphaHBar ℚbar M H ℓ (genH f g hf hg hg0)
      = (⟨coeffEmb ℚbar ((⟨intSeriesC ℚ pf / intSeriesC ℚ pg,
            FB_le_FT M H ℓ (div_mem_qExpFunctionFieldC f g hf hg hg0)⟩ : FT M H ℓ) : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange ℚbar
            (⟨intSeriesC ℚ pf / intSeriesC ℚ pg,
              FB_le_FT M H ℓ (div_mem_qExpFunctionFieldC f g hf hg hg0)⟩ : FT M H ℓ).2⟩ :
            laurentBaseChange ℚbar (FT M H ℓ)) := by
    apply Subtype.ext
    rw [coe_heckeAlphaHBar]
    rfl
  rw [e1, hτ, coe_heckeAlphaHBar, hy, tau0_incl_generator hσd hγ hγd f g hf hg hg0 hy]

include hσd hγd hγ' hγ'd hc hτ in

theorem comp_beta_eq (Kβ : HeckeBetaHDefined M H ℓ) :
    (τ : laurentBaseChange ℚbar (FT M H ℓ) →ₐ[ℚbar] laurentBaseChange ℚbar (FT M H ℓ)).comp
        (heckeBetaHBar ℚbar M H ℓ)
      = (heckeBetaHBar ℚbar M H ℓ).comp
          (σd : xHFunctionFieldBar M H →ₐ[ℚbar] xHFunctionFieldBar M H) := by
  have Kβ' : ∀ y ∈ FB M H, qExpand ℚ ℓ y ∈ FT M H ℓ := Kβ
  refine IntermediateField.algHom_ext_of_eq_adjoin (F := ℚbar)
    (s := ⇑(coeffEmb ℚbar) '' intFormRatiosC ℚ (CohCarrier.GammaH M H))
    (laurentBaseChange_eq_adjoin_ratios M H) ?_
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ := hx
  obtain ⟨y, hyF, hy, -⟩ := witness hσd hγ' hγ'd f g hf hg hg0
  apply Subtype.ext
  show ((τ (heckeBetaHBar ℚbar M H ℓ (genH f g hf hg hg0)) : laurentBaseChange ℚbar (FT M H ℓ)) :
      LaurentSeries ℚbar)
    = ((heckeBetaHBar ℚbar M H ℓ (σd (genH f g hf hg hg0)) : laurentBaseChange ℚbar (FT M H ℓ)) :
      LaurentSeries ℚbar)
  have hmem : qExpand ℚ ℓ (intSeriesC ℚ pf / intSeriesC ℚ pg) ∈ FT M H ℓ :=
    Kβ' _ (div_mem_qExpFunctionFieldC f g hf hg hg0)
  have e1 : heckeBetaHBar ℚbar M H ℓ (genH f g hf hg hg0)
      = (⟨coeffEmb ℚbar ((⟨qExpand ℚ ℓ (intSeriesC ℚ pf / intSeriesC ℚ pg), hmem⟩ : FT M H ℓ) :
            LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange ℚbar hmem⟩ :
          laurentBaseChange ℚbar (FT M H ℓ)) := by
    apply Subtype.ext
    rw [coe_heckeBetaHBar M H ℓ Kβ]
    exact (coeffEmb_qExpand ℚbar ℓ _).symm
  rw [e1, hτ, coe_heckeBetaHBar M H ℓ Kβ, hy, ← coeffEmb_qExpand,
    tau0_qExpand_generator hσd hγ hγ' hγ'd hc f g hf hg hg0 hmem hy]

end Main

-- `FT M H ℓ` and `xHTopFunctionFieldC ℚ M H (M * ℓ)` are the same field, but the
-- latter is a `def`; the pin's lakefile compares types at `.all` transparency
-- globally, so its `main` needs no such hint. Scoped here, as the port does in
-- `X1/DiamondAut.lean`/`X1/Inputs.lean`.
set_option backward.isDefEq.respectTransparency.types false in
theorem main (M ℓ : ℕ) [NeZero M] [NeZero ℓ] (H : Subgroup (ZMod M)ˣ) (d : (ZMod M)ˣ) :
    ∃ τ : laurentBaseChange ℚbar (xHTopFunctionFieldC ℚ M H (M * ℓ)) ≃ₐ[ℚbar]
        laurentBaseChange ℚbar (xHTopFunctionFieldC ℚ M H (M * ℓ)),
      SemilinearAut.IntertwinesAlong (heckeAlphaHBar ℚbar M H ℓ).toRingHom
          (SemilinearAut.ofAlgAut (diamondAutHBar M H d)) (SemilinearAut.ofAlgAut τ) ∧
        SemilinearAut.IntertwinesAlong (heckeBetaHBar ℚbar M H ℓ).toRingHom
          (SemilinearAut.ofAlgAut (diamondAutHBar M H d)) (SemilinearAut.ofAlgAut τ) := by
  by_cases hex : ∃ σ : xHFunctionFieldBar M H ≃ₐ[ℚbar] xHFunctionFieldBar M H, IsDiamondAutHBar M H d σ
  · have hσd : IsDiamondAutHBar M H d (diamondAutHBar M H d) := isDiamondAutHBar_diamondAutHBar hex
    obtain ⟨γ, γ', hγ, hγ', hγd, hγ'd, hc⟩ := exists_gammas M ℓ (ZMod.val_coe_unit_coprime d)
    rw [ZMod.natCast_zmod_val] at hγd hγ'd
    obtain ⟨τ, hτ⟩ := ModularCurve.exists_algEquiv_laurentBaseChange_cover ℚbar (FT M H ℓ)
      (sigma (rationalSlash_level M H ℓ) γ hγ)
    have Iα : SemilinearAut.IntertwinesAlong (heckeAlphaHBar ℚbar M H ℓ).toRingHom
        (SemilinearAut.ofAlgAut (diamondAutHBar M H d)) (SemilinearAut.ofAlgAut τ) := by
      intro x
      rw [SemilinearAut.ofAlgAut_smul, SemilinearAut.ofAlgAut_smul]
      exact AlgHom.congr_fun (comp_alpha_eq M ℓ H d hσd hγ hγd τ hτ) x
    refine ⟨τ, Iα, ?_⟩
    by_cases Kβ : HeckeBetaHDefined M H ℓ
    · intro x
      rw [SemilinearAut.ofAlgAut_smul, SemilinearAut.ofAlgAut_smul]
      exact AlgHom.congr_fun (comp_beta_eq M ℓ H d hσd hγ hγ' hγd hγ'd hc τ hτ Kβ) x
    · rw [heckeBetaHBar_of_not M H ℓ Kβ]
      exact Iα
  · have h0 : diamondAutHBar M H d = AlgEquiv.refl := diamondAutHBar_of_not hex
    refine ⟨AlgEquiv.refl, fun x => ?_, fun x => ?_⟩ <;>
      simp only [h0, SemilinearAut.ofAlgAut_smul, AlgEquiv.coe_refl, id_eq]

end XH

end DiamondLift

/-- The diamond automorphism of `X_H(M)` at `d` intertwines the α/β Hecke
degeneracy maps of `X_H(M) → X_H(M) ∩ X₀(Mℓ)`, after base change to `ℚ̄`. -/
theorem exists_algEquiv_intertwinesAlong_diamondAutHBar (M : ℕ) [NeZero M]
    (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) [NeZero ℓ] (d : (ZMod M)ˣ) :
    ∃ τ : laurentBaseChange (AlgebraicClosure ℚ) (xHTopFunctionFieldC ℚ M H (M * ℓ))
        ≃ₐ[AlgebraicClosure ℚ]
        laurentBaseChange (AlgebraicClosure ℚ) (xHTopFunctionFieldC ℚ M H (M * ℓ)),
      SemilinearAut.IntertwinesAlong
          (heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ).toRingHom
          (SemilinearAut.ofAlgAut (diamondAutHBar M H d))
          (SemilinearAut.ofAlgAut τ) ∧
        SemilinearAut.IntertwinesAlong
          (heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ).toRingHom
          (SemilinearAut.ofAlgAut (diamondAutHBar M H d))
          (SemilinearAut.ofAlgAut τ) :=
  DiamondLift.XH.main M ℓ H d

end ModularCurve

end
