/-
The `X₁(M)` specialisation of the diamond-lift engine (`XH/DiamondLiftPrelude.lean`)
and the headline `ModularCurve.exists_algEquiv_intertwinesAlong_diamondAutBar`.

This is the level-specific half of
`P2M/Sol/S_ModularCurve_exists_algEquiv_intertwinesAlong_diamondAutBar.lean`
(pin `aa2d8b3`): the `Γ₁(M)`-level instances and cocycle, `rationalSlash_level`
for `Γ₁(M) ⊓ Γ₀(Mℓ)`, the `Genuine` block (`toC_sigma0_generator`/`tau0_incl*`/
`tau0_qExpand*`/`exists_tau0`), `isBaseChangeAutOf_diamondAutBar` and `main` over
the base change `ℚ̄`. Its sibling `XH/DiamondLift.lean` is the `Γ_H(M)` case.

https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_exists_algEquiv_intertwinesAlong_diamondAutBar.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_exists_algEquiv_intertwinesAlong_diamondAutBar.lean
-/
import FLTForHuman.ModularCurve.XH.DiamondLiftPrelude
import FLTForHuman.ModularCurve.X1.HeckeOperator
import FLTForHuman.ModularCurve.X1.Diamond
import FLTForHuman.ModularCurve.X1.DiamondAut
import FLTForHuman.ModularCurve.X1.BaseChangeCover
import FLTForHuman.ModularForms.Level.Diamond

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 1600000
set_option linter.style.haveILetI false

noncomputable section

open UpperHalfPlane ModularForm CongruenceSubgroup OnePoint Function HahnSeries AlgebraicCurve
open scoped MatrixGroups ModularForm Manifold

namespace ModularCurve

namespace DiamondLift

namespace X1

local notation "GL↑(" Γ ")" => ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))
local notation "ℚbar" => AlgebraicClosure ℚ

/-! ## The `Γ₁(M) ⊓ Γ₀(Mℓ)` level -/

scoped instance isLevel_Gamma1 (M : ℕ) : IsLevel (Gamma1 M) :=
  ⟨by simp⟩

scoped instance isLevel_Gamma1_inf_Gamma0 (M t : ℕ) : IsLevel (Gamma1 M ⊓ Gamma0 t) :=
  ⟨⟨by simp, by simp [Gamma0_mem]⟩⟩

scoped instance normalizes_Gamma0_Gamma1 (M : ℕ) : Normalizes (Gamma0 M) (Gamma1 M) :=
  ⟨fun _ _ hγ hA => ModularForm.Level.conj_mem_Gamma1 hγ hA⟩

scoped instance normalizes_level (M ℓ : ℕ) : Normalizes (Gamma0 (M * ℓ)) (Gamma1 M ⊓ Gamma0 (M * ℓ)) :=
  ⟨fun _ _ hγ hA => ⟨ModularForm.Level.conj_mem_Gamma1 (Gamma0_mul_le M ℓ hγ) hA.1,
    (Gamma0 (M * ℓ)).mul_mem ((Gamma0 (M * ℓ)).mul_mem hγ hA.2) ((Gamma0 (M * ℓ)).inv_mem hγ)⟩⟩

scoped instance finiteIndex_level (M ℓ : ℕ) [NeZero M] [NeZero ℓ] :
    (Gamma1 M ⊓ Gamma0 (M * ℓ)).FiniteIndex := by
  haveI := neZero_mul M ℓ
  infer_instance

theorem cocycle (M ℓ : ℕ) [NeZero ℓ] : ∀ γ ∈ Gamma1 M ⊓ Gamma0 (M * ℓ), ∃ γ₁ ∈ Gamma1 M,
    γ₁ 0 0 = γ 0 0 ∧ γ₁ 0 1 = (ℓ : ℤ) * γ 0 1 ∧ (ℓ : ℤ) * γ₁ 1 0 = γ 1 0 ∧ γ₁ 1 1 = γ 1 1 := by
  intro γ hγ
  obtain ⟨hγ1, hγ0⟩ := Subgroup.mem_inf.mp hγ
  have hdet : (γ 0 0 : ℤ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.det_coe; rwa [Matrix.det_fin_two] at this
  have hMℓc : ((M * ℓ : ℕ) : ℤ) ∣ γ 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hγ0)
  obtain ⟨c', hc'⟩ := hMℓc
  rw [Nat.cast_mul] at hc'
  have hdet' : Matrix.det !![(γ 0 0 : ℤ), (ℓ : ℤ) * γ 0 1; (M : ℤ) * c', γ 1 1] = 1 := by
    rw [Matrix.det_fin_two_of]; linear_combination hdet + (γ 0 1 : ℤ) * hc'
  -- See the sibling `XH/DiamondLift.lean` (`cocycle`): v4.34 does not elaborate
  -- the bare `⟨_, hdet'⟩` against `SL(2, ℤ)` as an argument of `Gamma1_mem`.
  let γ₁ : SL(2, ℤ) := ⟨!![(γ 0 0 : ℤ), (ℓ : ℤ) * γ 0 1; (M : ℤ) * c', γ 1 1], hdet'⟩
  have h1 : γ₁ ∈ Gamma1 M := by
    rw [Gamma1_mem] at hγ1 ⊢
    obtain ⟨h00, h11, -⟩ := hγ1
    refine ⟨h00, h11, ?_⟩
    show (((M : ℤ) * c' : ℤ) : ZMod M) = 0
    push_cast; rw [ZMod.natCast_self, zero_mul]
  refine ⟨γ₁, h1, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · show (ℓ : ℤ) * ((M : ℤ) * c') = γ 1 0
    linear_combination -hc'
  · rfl

theorem rationalSlash_level (M ℓ : ℕ) [NeZero M] [NeZero ℓ] :
    RationalSlash (Gamma1 M ⊓ Gamma0 (M * ℓ)) (Gamma0 (M * ℓ)) := by
  intro k f p hp γ hγ
  haveI := neZero_mul M ℓ
  have hle : Gamma1 (M * ℓ) ≤ Gamma1 M ⊓ Gamma0 (M * ℓ) :=
    le_inf (Gamma1_le_of_dvd (dvd_mul_right M ℓ)) (Gamma1_in_Gamma0 _)
  have hle' : GL↑(Gamma1 (M * ℓ)) ≤ GL↑(Gamma1 M ⊓ Gamma0 (M * ℓ)) := Subgroup.map_mono hle
  obtain ⟨D, f₁, p₁, hD, hp₁, hf₁⟩ :=
    ModularCurve.exists_isIntegralQExp_smul_slash_of_mem_Gamma0 (M * ℓ) (restrictForm hle' f)
      (by rw [IsIntegralQExp, coe_restrictForm]; exact hp) γ hγ
  refine ⟨D, (D : ℂ) • slashForm γ hγ f, p₁, hD, ?_, ?_⟩
  · have : (⇑((D : ℂ) • slashForm γ hγ f) : ℍ → ℂ) = ⇑f₁ := by
      rw [FunLike.coe_smul, coe_slashForm_SL, hf₁, coe_restrictForm]
    rw [IsIntegralQExp, this]
    exact hp₁
  · rw [FunLike.coe_smul, coe_slashForm_SL]

abbrev FB (M : ℕ) : IntermediateField ℚ (LaurentSeries ℚ) := qExpFunctionFieldC ℚ (Gamma1 M)

abbrev FT (M ℓ : ℕ) : IntermediateField ℚ (LaurentSeries ℚ) :=
  qExpFunctionFieldC ℚ (Gamma1 M ⊓ Gamma0 (M * ℓ))

theorem FB_le_FT (M ℓ : ℕ) : FB M ≤ FT M ℓ :=
  qExpFunctionFieldC_mono ℚ inf_le_left

/-! ## The genuine diamond lift on `Γ₁(M)` -/

section Genuine

variable {M ℓ : ℕ} [NeZero M] [NeZero ℓ] {d : ℕ}
  {σ₀ : x1FunctionField M ≃ₐ[ℚ] x1FunctionField M} (hσ₀ : IsDiamondAut M d σ₀)
  {γ γ' : SL(2, ℤ)} (hγ : γ ∈ Gamma0 (M * ℓ)) (hγ' : γ' ∈ Gamma0 M)
  (hγd : ((γ 0 0 : ℤ) : ZMod M) = d) (hγ'd : ((γ' 0 0 : ℤ) : ZMod M) = d)
  (hc : heckeDiagMatrix ℓ * Matrix.SpecialLinearGroup.mapGL ℝ γ
    = Matrix.SpecialLinearGroup.mapGL ℝ γ' * heckeDiagMatrix ℓ)

include hσ₀ in

theorem toC_sigma0_generator {γ₀ : SL(2, ℤ)} (hγ₀ : γ₀ ∈ Gamma0 M)
    (hγ₀d : ((γ₀ 0 0 : ℤ) : ZMod M) = d) {k : ℤ}
    (f g : ModularForm GL↑(Gamma1 M) k) {pf pg : PowerSeries ℤ}
    (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0) :
    toC ((σ₀ ⟨intSeriesC ℚ pf / intSeriesC ℚ pg, div_mem_qExpFunctionFieldC f g hf hg hg0⟩ :
        x1FunctionField M) : LaurentSeries ℚ)
      = qC ((⇑f : ℍ → ℂ) ∣[k] γ₀) / qC ((⇑g : ℍ → ℂ) ∣[k] γ₀) := by
  have H := hσ₀.2 k f g pf pg hf hg hg0 γ₀ hγ₀ hγ₀d
  rw [eq_div_iff (qC_slash_ne_zero (Γ := Gamma1 M) γ₀ hγ₀ (qC_ne_zero_of_intSeriesC_ne_zero hg hg0))]
  exact H

include hσ₀ hγd in

theorem tau0_incl_generator {k : ℤ} (f g : ModularForm GL↑(Gamma1 M) k) {pf pg : PowerSeries ℤ}
    (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0) :
    ((sigma (rationalSlash_level M ℓ) γ hγ
        ⟨intSeriesC ℚ pf / intSeriesC ℚ pg, FB_le_FT M ℓ (div_mem_qExpFunctionFieldC f g hf hg hg0)⟩ :
          FT M ℓ) : LaurentSeries ℚ)
      = ((σ₀ ⟨intSeriesC ℚ pf / intSeriesC ℚ pg, div_mem_qExpFunctionFieldC f g hf hg hg0⟩ :
          x1FunctionField M) : LaurentSeries ℚ) := by
  apply toC_injective
  have hle' : GL↑(Gamma1 M ⊓ Gamma0 (M * ℓ)) ≤ GL↑(Gamma1 M) := Subgroup.map_mono inf_le_left
  have hf' : IsIntegralQExp (restrictForm hle' f) pf := by
    rw [IsIntegralQExp, coe_restrictForm]; exact hf
  have hg' : IsIntegralQExp (restrictForm hle' g) pg := by
    rw [IsIntegralQExp, coe_restrictForm]; exact hg
  have h1 := toC_sigma_generator (rationalSlash_level M ℓ) γ hγ (restrictForm hle' f)
    (restrictForm hle' g) hf' hg' hg0
  rw [coe_restrictForm, coe_restrictForm] at h1
  rw [toC_sigma0_generator hσ₀ (Gamma0_mul_le M ℓ hγ) hγd f g hf hg hg0]
  exact h1

include hσ₀ hγd in

theorem tau0_incl (y : LaurentSeries ℚ) (hy : y ∈ FB M) :
    ((sigma (rationalSlash_level M ℓ) γ hγ ⟨y, FB_le_FT M ℓ hy⟩ : FT M ℓ) : LaurentSeries ℚ)
      = ((σ₀ ⟨y, hy⟩ : x1FunctionField M) : LaurentSeries ℚ) := by
  let incl : FB M →+* FT M ℓ :=
    (algebraMap (FB M) (LaurentSeries ℚ)).codRestrict (FT M ℓ) (fun z => FB_le_FT M ℓ z.2)
  let φ : FB M →+* LaurentSeries ℚ :=
    (algebraMap (FT M ℓ) (LaurentSeries ℚ)).comp
      ((sigma (rationalSlash_level M ℓ) γ hγ).toRingHom.comp incl)
  let ψ : FB M →+* LaurentSeries ℚ :=
    (algebraMap (FB M) (LaurentSeries ℚ)).comp σ₀.toRingEquiv.toRingHom
  have H : φ = ψ := by
    refine ringHom_ext_adjoin φ ψ ?_
    intro x hx
    obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ := hx
    exact tau0_incl_generator hσ₀ hγ hγd f g hf hg hg0
  exact RingHom.congr_fun H ⟨y, hy⟩

include hσ₀ hγ' hγ'd hc in

theorem tau0_qExpand_generator {k : ℤ} (f g : ModularForm GL↑(Gamma1 M) k) {pf pg : PowerSeries ℤ}
    (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0)
    (hmem : qExpand ℚ ℓ (intSeriesC ℚ pf / intSeriesC ℚ pg) ∈ FT M ℓ) :
    ((sigma (rationalSlash_level M ℓ) γ hγ ⟨qExpand ℚ ℓ (intSeriesC ℚ pf / intSeriesC ℚ pg), hmem⟩ :
          FT M ℓ) : LaurentSeries ℚ)
      = qExpand ℚ ℓ ((σ₀ ⟨intSeriesC ℚ pf / intSeriesC ℚ pg, div_mem_qExpFunctionFieldC f g hf hg hg0⟩ :
          x1FunctionField M) : LaurentSeries ℚ) := by
  have hℓ : ℓ ≠ 0 := NeZero.ne ℓ
  apply toC_injective

  have hSf : IsIntegralQExp (stretch (Γ' := Gamma1 M ⊓ Gamma0 (M * ℓ)) (cocycle M ℓ) hℓ f)
      (expandPS ℓ pf) := isIntegralQExp_stretch _ hℓ f hf
  have hSg : IsIntegralQExp (stretch (Γ' := Gamma1 M ⊓ Gamma0 (M * ℓ)) (cocycle M ℓ) hℓ g)
      (expandPS ℓ pg) := isIntegralQExp_stretch _ hℓ g hg
  have hSg0 : intSeriesC ℚ (expandPS ℓ pg) ≠ 0 := by
    rw [intSeriesC_expandPS]
    exact fun h => hg0 (ModularCurve.qExpand_injective ℓ (by rw [h, map_zero]))
  have hx : (⟨qExpand ℚ ℓ (intSeriesC ℚ pf / intSeriesC ℚ pg), hmem⟩ : FT M ℓ)
      = ⟨intSeriesC ℚ (expandPS ℓ pf) / intSeriesC ℚ (expandPS ℓ pg),
          div_mem_qExpFunctionFieldC _ _ hSf hSg hSg0⟩ := by
    apply Subtype.ext
    show qExpand ℚ ℓ (intSeriesC ℚ pf / intSeriesC ℚ pg)
      = intSeriesC ℚ (expandPS ℓ pf) / intSeriesC ℚ (expandPS ℓ pg)
    rw [map_div₀, intSeriesC_expandPS, intSeriesC_expandPS]
  rw [hx, toC_sigma_generator (rationalSlash_level M ℓ) γ hγ _ _ hSf hSg hSg0]

  rw [stretch_slash (cocycle M ℓ) hℓ f hγ' hc, stretch_slash (cocycle M ℓ) hℓ g hγ' hc,
    qC_stretch, qC_stretch, ← map_div₀, coe_slashForm_SL, coe_slashForm_SL,
    ← toC_sigma0_generator hσ₀ hγ' hγ'd f g hf hg hg0, toC_qExpand]

include hσ₀ hγ' hγ'd hc in

theorem tau0_qExpand (Kβ : ∀ y ∈ FB M, qExpand ℚ ℓ y ∈ FT M ℓ) (y : LaurentSeries ℚ)
    (hy : y ∈ FB M) :
    ((sigma (rationalSlash_level M ℓ) γ hγ ⟨qExpand ℚ ℓ y, Kβ y hy⟩ : FT M ℓ) : LaurentSeries ℚ)
      = qExpand ℚ ℓ ((σ₀ ⟨y, hy⟩ : x1FunctionField M) : LaurentSeries ℚ) := by
  let qres : FB M →+* FT M ℓ :=
    ((qExpand ℚ ℓ).comp (algebraMap (FB M) (LaurentSeries ℚ))).codRestrict (FT M ℓ)
      (fun z => Kβ _ z.2)
  let φ : FB M →+* LaurentSeries ℚ :=
    (algebraMap (FT M ℓ) (LaurentSeries ℚ)).comp
      ((sigma (rationalSlash_level M ℓ) γ hγ).toRingHom.comp qres)
  let ψ : FB M →+* LaurentSeries ℚ :=
    (qExpand ℚ ℓ).comp ((algebraMap (FB M) (LaurentSeries ℚ)).comp σ₀.toRingEquiv.toRingHom)
  have H : φ = ψ := by
    refine ringHom_ext_adjoin φ ψ ?_
    intro x hx
    obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ := hx
    exact tau0_qExpand_generator hσ₀ hγ hγ' hγ'd hc f g hf hg hg0 _
  exact RingHom.congr_fun H ⟨y, hy⟩

end Genuine

theorem exists_tau0 (M ℓ : ℕ) [NeZero M] [NeZero ℓ] (d : ℕ) :
    ∃ τ₀ : FT M ℓ ≃+* FT M ℓ,
      (∀ (y : LaurentSeries ℚ) (hy : y ∈ FB M),
        ((τ₀ ⟨y, FB_le_FT M ℓ hy⟩ : FT M ℓ) : LaurentSeries ℚ)
          = ((diamondAut M d ⟨y, hy⟩ : x1FunctionField M) : LaurentSeries ℚ)) ∧
      (∀ (Kβ : ∀ y ∈ FB M, qExpand ℚ ℓ y ∈ FT M ℓ) (y : LaurentSeries ℚ) (hy : y ∈ FB M),
        ((τ₀ ⟨qExpand ℚ ℓ y, Kβ y hy⟩ : FT M ℓ) : LaurentSeries ℚ)
          = qExpand ℚ ℓ ((diamondAut M d ⟨y, hy⟩ : x1FunctionField M) : LaurentSeries ℚ)) := by
  by_cases hex : ∃ σ : x1FunctionField M ≃ₐ[ℚ] x1FunctionField M, IsDiamondAut M d σ
  · have hσ₀ : IsDiamondAut M d (diamondAut M d) := isDiamondAut_diamondAut hex
    obtain ⟨γ, γ', hγ, hγ', hγd, hγ'd, hc⟩ := exists_gammas M ℓ hσ₀.1
    exact ⟨sigma (rationalSlash_level M ℓ) γ hγ, fun y hy => tau0_incl hσ₀ hγ hγd y hy,
      fun Kβ y hy => tau0_qExpand hσ₀ hγ hγ' hγ'd hc Kβ y hy⟩
  · have h0 : diamondAut M d = AlgEquiv.refl := diamondAut_of_not hex
    refine ⟨RingEquiv.refl _, fun y hy => ?_, fun Kβ y hy => ?_⟩
    · have e1 : ((RingEquiv.refl (FT M ℓ) ⟨y, FB_le_FT M ℓ hy⟩ : FT M ℓ) : LaurentSeries ℚ) = y := rfl
      have e2 : ((diamondAut M d ⟨y, hy⟩ : x1FunctionField M) : LaurentSeries ℚ) = y := by
        rw [h0]; rfl
      exact e1.trans e2.symm
    · have e1 : ((RingEquiv.refl (FT M ℓ) ⟨qExpand ℚ ℓ y, Kβ y hy⟩ : FT M ℓ) : LaurentSeries ℚ)
          = qExpand ℚ ℓ y := rfl
      have e2 : ((diamondAut M d ⟨y, hy⟩ : x1FunctionField M) : LaurentSeries ℚ) = y := by
        rw [h0]; rfl
      rw [e1, e2]

/-! ## The base change to `ℚ̄` and the headline -/

theorem isBaseChangeAutOf_diamondAutBar (M d : ℕ) :
    IsBaseChangeAutOf ℚbar (diamondAut M d) (diamondAutBar M d) := by
  obtain ⟨τ, hτ⟩ := ModularCurve.exists_algEquiv_laurentBaseChange_cover ℚbar
    (x1FunctionField M) (diamondAut M d).toRingEquiv
  exact isBaseChangeAutOf_baseChangeAut ⟨τ, fun y => hτ y⟩

section Main

variable (M ℓ : ℕ) [NeZero M] [NeZero ℓ] (d : ℕ)
  (τ₀ : FT M ℓ ≃+* FT M ℓ)
  (h1 : ∀ (y : LaurentSeries ℚ) (hy : y ∈ FB M),
    ((τ₀ ⟨y, FB_le_FT M ℓ hy⟩ : FT M ℓ) : LaurentSeries ℚ)
      = ((diamondAut M d ⟨y, hy⟩ : x1FunctionField M) : LaurentSeries ℚ))
  (h2 : ∀ (Kβ : ∀ y ∈ FB M, qExpand ℚ ℓ y ∈ FT M ℓ) (y : LaurentSeries ℚ) (hy : y ∈ FB M),
    ((τ₀ ⟨qExpand ℚ ℓ y, Kβ y hy⟩ : FT M ℓ) : LaurentSeries ℚ)
      = qExpand ℚ ℓ ((diamondAut M d ⟨y, hy⟩ : x1FunctionField M) : LaurentSeries ℚ))
  (τ : laurentBaseChange ℚbar (FT M ℓ) ≃ₐ[ℚbar] laurentBaseChange ℚbar (FT M ℓ))
  (hτ : ∀ y : FT M ℓ,
    ((τ ⟨coeffEmb ℚbar (y : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange ℚbar y.2⟩ :
        laurentBaseChange ℚbar (FT M ℓ)) : LaurentSeries ℚbar)
      = coeffEmb ℚbar ((τ₀ y : FT M ℓ) : LaurentSeries ℚ))

include h1 hτ in

theorem comp_alpha_eq :
    (τ : laurentBaseChange ℚbar (FT M ℓ) →ₐ[ℚbar] laurentBaseChange ℚbar (FT M ℓ)).comp
        (heckeAlphaOneBar ℚbar M ℓ)
      = (heckeAlphaOneBar ℚbar M ℓ).comp
          (diamondAutBar M d : x1FunctionFieldBar M →ₐ[ℚbar] x1FunctionFieldBar M) := by
  have hσ := isBaseChangeAutOf_diamondAutBar M d
  refine IntermediateField.algHom_ext_of_eq_adjoin (F := ℚbar)
    (s := ⇑(coeffEmb ℚbar) '' ((x1FunctionField M) : Set (LaurentSeries ℚ))) rfl ?_
  rintro _ ⟨y, hy, rfl⟩
  apply Subtype.ext
  show ((τ (heckeAlphaOneBar ℚbar M ℓ ⟨coeffEmb ℚbar y, coeffEmb_mem_laurentBaseChange ℚbar hy⟩) :
        laurentBaseChange ℚbar (FT M ℓ)) : LaurentSeries ℚbar)
    = ((heckeAlphaOneBar ℚbar M ℓ
        (diamondAutBar M d ⟨coeffEmb ℚbar y, coeffEmb_mem_laurentBaseChange ℚbar hy⟩) :
          laurentBaseChange ℚbar (FT M ℓ)) : LaurentSeries ℚbar)
  have e1 : heckeAlphaOneBar ℚbar M ℓ ⟨coeffEmb ℚbar y, coeffEmb_mem_laurentBaseChange ℚbar hy⟩
      = (⟨coeffEmb ℚbar ((⟨y, FB_le_FT M ℓ hy⟩ : FT M ℓ) : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange ℚbar (⟨y, FB_le_FT M ℓ hy⟩ : FT M ℓ).2⟩ :
            laurentBaseChange ℚbar (FT M ℓ)) :=
    Subtype.ext (coe_heckeAlphaOneBar M ℓ _)
  have e2 : ((diamondAutBar M d ⟨coeffEmb ℚbar y, coeffEmb_mem_laurentBaseChange ℚbar hy⟩ :
      x1FunctionFieldBar M) : LaurentSeries ℚbar)
        = coeffEmb ℚbar ((diamondAut M d ⟨y, hy⟩ : x1FunctionField M) : LaurentSeries ℚ) :=
    hσ ⟨y, hy⟩
  rw [e1, hτ, coe_heckeAlphaOneBar, e2, h1 y hy]

include h1 h2 hτ in

theorem comp_beta_eq (Kβ : HeckeBetaOneDefined M ℓ) :
    (τ : laurentBaseChange ℚbar (FT M ℓ) →ₐ[ℚbar] laurentBaseChange ℚbar (FT M ℓ)).comp
        (heckeBetaOneBar ℚbar M ℓ)
      = (heckeBetaOneBar ℚbar M ℓ).comp
          (diamondAutBar M d : x1FunctionFieldBar M →ₐ[ℚbar] x1FunctionFieldBar M) := by
  have hσ := isBaseChangeAutOf_diamondAutBar M d
  have Kβ' : ∀ y ∈ FB M, qExpand ℚ ℓ y ∈ FT M ℓ := Kβ
  refine IntermediateField.algHom_ext_of_eq_adjoin (F := ℚbar)
    (s := ⇑(coeffEmb ℚbar) '' ((x1FunctionField M) : Set (LaurentSeries ℚ))) rfl ?_
  rintro _ ⟨y, hy, rfl⟩
  apply Subtype.ext
  show ((τ (heckeBetaOneBar ℚbar M ℓ ⟨coeffEmb ℚbar y, coeffEmb_mem_laurentBaseChange ℚbar hy⟩) :
        laurentBaseChange ℚbar (FT M ℓ)) : LaurentSeries ℚbar)
    = ((heckeBetaOneBar ℚbar M ℓ
        (diamondAutBar M d ⟨coeffEmb ℚbar y, coeffEmb_mem_laurentBaseChange ℚbar hy⟩) :
          laurentBaseChange ℚbar (FT M ℓ)) : LaurentSeries ℚbar)
  have e1 : heckeBetaOneBar ℚbar M ℓ ⟨coeffEmb ℚbar y, coeffEmb_mem_laurentBaseChange ℚbar hy⟩
      = (⟨coeffEmb ℚbar ((⟨qExpand ℚ ℓ y, Kβ' y hy⟩ : FT M ℓ) : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange ℚbar (Kβ' y hy)⟩ : laurentBaseChange ℚbar (FT M ℓ)) := by
    apply Subtype.ext
    rw [coe_heckeBetaOneBar M ℓ Kβ]
    exact (coeffEmb_qExpand ℚbar ℓ y).symm
  have e2 : ((diamondAutBar M d ⟨coeffEmb ℚbar y, coeffEmb_mem_laurentBaseChange ℚbar hy⟩ :
      x1FunctionFieldBar M) : LaurentSeries ℚbar)
        = coeffEmb ℚbar ((diamondAut M d ⟨y, hy⟩ : x1FunctionField M) : LaurentSeries ℚ) :=
    hσ ⟨y, hy⟩
  rw [e1, hτ, coe_heckeBetaOneBar M ℓ Kβ, e2, ← coeffEmb_qExpand, h2 Kβ' y hy]

end Main

-- See the sibling `XH/DiamondLift.lean` (`main`): `FT M ℓ` and
-- `x1x0FunctionFieldC ℚ M (M * ℓ)` are the same field spelled with two different
-- `def`s, which the pin's lakefile compares at `.all` transparency globally.
set_option backward.isDefEq.respectTransparency.types false in
theorem main (M ℓ : ℕ) [NeZero M] [NeZero ℓ] (d : ℕ) :
    ∃ τ : laurentBaseChange ℚbar (x1x0FunctionFieldC ℚ M (M * ℓ)) ≃ₐ[ℚbar]
        laurentBaseChange ℚbar (x1x0FunctionFieldC ℚ M (M * ℓ)),
      SemilinearAut.IntertwinesAlong (heckeAlphaOneBar ℚbar M ℓ).toRingHom
          (SemilinearAut.ofAlgAut (diamondAutBar M d)) (SemilinearAut.ofAlgAut τ) ∧
        SemilinearAut.IntertwinesAlong (heckeBetaOneBar ℚbar M ℓ).toRingHom
          (SemilinearAut.ofAlgAut (diamondAutBar M d)) (SemilinearAut.ofAlgAut τ) := by
  obtain ⟨τ₀, h1, h2⟩ := exists_tau0 M ℓ d
  obtain ⟨τ, hτ⟩ := ModularCurve.exists_algEquiv_laurentBaseChange_cover ℚbar (FT M ℓ) τ₀
  have Iα : SemilinearAut.IntertwinesAlong (heckeAlphaOneBar ℚbar M ℓ).toRingHom
      (SemilinearAut.ofAlgAut (diamondAutBar M d)) (SemilinearAut.ofAlgAut τ) := by
    intro x
    rw [SemilinearAut.ofAlgAut_smul, SemilinearAut.ofAlgAut_smul]
    exact AlgHom.congr_fun (comp_alpha_eq M ℓ d τ₀ h1 τ hτ) x
  refine ⟨τ, Iα, ?_⟩
  by_cases Kβ : HeckeBetaOneDefined M ℓ
  · intro x
    rw [SemilinearAut.ofAlgAut_smul, SemilinearAut.ofAlgAut_smul]
    exact AlgHom.congr_fun (comp_beta_eq M ℓ d τ₀ h1 h2 τ hτ Kβ) x
  · rw [heckeBetaOneBar_of_not M ℓ Kβ]
    exact Iα

end X1

end DiamondLift

/-- The diamond automorphism of `X₁(M)` at `d` intertwines the α/β Hecke
degeneracy maps of `X₁(M) → X₁(M) ∩ X₀(Mℓ)`, after base change to `ℚ̄`. -/
theorem exists_algEquiv_intertwinesAlong_diamondAutBar (M : ℕ) [NeZero M] (ℓ : ℕ)
    [NeZero ℓ] (d : ℕ) :
    ∃ τ : laurentBaseChange (AlgebraicClosure ℚ) (x1x0FunctionFieldC ℚ M (M * ℓ))
        ≃ₐ[AlgebraicClosure ℚ]
        laurentBaseChange (AlgebraicClosure ℚ) (x1x0FunctionFieldC ℚ M (M * ℓ)),
      SemilinearAut.IntertwinesAlong (heckeAlphaOneBar (AlgebraicClosure ℚ) M ℓ).toRingHom
          (SemilinearAut.ofAlgAut (diamondAutBar M d))
          (SemilinearAut.ofAlgAut τ) ∧
        SemilinearAut.IntertwinesAlong (heckeBetaOneBar (AlgebraicClosure ℚ) M ℓ).toRingHom
          (SemilinearAut.ofAlgAut (diamondAutBar M d))
          (SemilinearAut.ofAlgAut τ) :=
  DiamondLift.X1.main M ℓ d

end ModularCurve

end
