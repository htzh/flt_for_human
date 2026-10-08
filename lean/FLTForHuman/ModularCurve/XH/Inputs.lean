/-
The capstone of the `X_H(M)` Hecke/diamond effort:
`ModularCurve.HeckeDiamondInputsHAll`.

For every prime `ℓ` the `X_H(M)` Hecke inputs `HeckeInputsHAlong (AlgebraicClosure ℚ) M H ℓ`
hold, and for every `d : (ZMod M)ˣ` there is a diamond automorphism of
`xHFunctionFieldBar M H` satisfying `IsDiamondAutHBar`.

This is the pin's assembly `P2M/Sol/S_ModularCurve_heckeDiamondInputsHAll.lean`
(pinned `aa2d8b3`), written by the manager as the effort's final wire test
([TOPIC-xH-hecke-diamond-inputs.md](../../topics/hecke/TOPIC-xH-hecke-diamond-inputs.md)
§5 SET-H-C). Two blocks of the pin do **not** need porting:

* the Hecke half is the dispatched headline `ModularCurve.heckeInputsHAlong`
  (`XH/HeckeInputs.lean`), where the pin re-derives the whole `A2HDIH` block a
  second time;
* the diamond half's engine — the pin's 586-line `A2HDIA` block, a third copy of the
  `slashForm`/`qC`/`IsImg`/`σfun`/`σAlgEquiv` machinery at `Γ_H(M)` — is replaced by
  the general-`Γ` engine of `XH/DiamondLiftPrelude.lean` (SET-H-B), instantiated at
  `Γ = Γ_H(M)`, `Δ = Γ₀(M)`.

The one gap is the *shape* of the engine's `RationalSlash`, which asks for a
`Γ_H(M)`-form `f₁` with `⇑f₁ = D • (⇑f ∣[k] γ)`; `exists_isIntegralQExp_smul_slash_of_mem_Gamma0`
supplies only a `Γ₁(M)`-form, and `Γ₁(M) ≤ Γ_H(M)` cannot be pushed the other way.
`rationalSlash_GammaH` closes it by taking `f₁ := D • slashForm γ hγ f`, a `Γ_H(M)`-form
because `Γ₀(M)` normalizes `Γ_H(M)` — i.e. the pin's weak `A2HDIA.SlashRational` plus
one line. `exists_ringEquiv_of_rationalSlash` is then the pin's
`A2HDIA.exists_algEquiv_of_slashRational` with the engine's `sigma` in place of
`σAlgEquiv`; the pin's `AlgEquiv` is only ever consumed as `σ₀.toRingEquiv`
(`exists_algEquiv_laurentBaseChange_cover` takes a `RingEquiv`), so a `RingEquiv` is
carried instead.

Every helper here stays `private`: the module's only public surface is
`ModularCurve.heckeDiamondInputsHAll`, as in `X1/Inputs.lean`.

FLT provenance, pinned `aa2d8b3`:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_heckeDiamondInputsHAll.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_heckeDiamondInputsHAll.lean
-/
import FLTForHuman.ModularCurve.XH.HeckeInputs
import FLTForHuman.ModularCurve.XH.DiamondLift
import FLTForHuman.ModularCurve.X1.BaseChangeCover

set_option autoImplicit false
set_option linter.unusedSectionVars false

-- The pin's `haveI` in the bundle's `∀ ℓ` half is load-bearing; keep it literal.
set_option linter.style.haveILetI false

noncomputable section

open UpperHalfPlane CongruenceSubgroup ModularForm OnePoint HahnSeries
open scoped MatrixGroups ModularForm

namespace ModularCurve

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)

private instance instIsLevelGammaH : DiamondLift.IsLevel (CohCarrier.GammaH M H) :=
  ⟨CohCarrier.translation_mem_GammaH M H⟩

private instance instNormalizesGammaH : DiamondLift.Normalizes (Gamma0 M) (CohCarrier.GammaH M H) :=
  ⟨fun _ _ hγ hA => CohCarrier.conj_mem_GammaH M H ⟨_, hγ⟩ ⟨_, hA⟩⟩

/-- The general engine's `RationalSlash` at `Γ_H(M)` and `Γ₀(M)`: the pin's
`A2HDIA.SlashRational` (its weak, `f₁`-free form) upgraded by taking
`f₁ := D • slashForm γ hγ f`, a `Γ_H(M)`-form because `Γ₀(M)` normalizes `Γ_H(M)`. -/
private theorem rationalSlash_GammaH :
    DiamondLift.RationalSlash (CohCarrier.GammaH M H) (Gamma0 M) := by
  intro k f p hp γ hγ
  have hle : ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))
      ≤ ((CohCarrier.GammaH M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) :=
    Subgroup.map_mono (CohCarrier.Gamma1_le_GammaH M H)
  obtain ⟨D, f₁, p₁, hD, hp₁, hf₁⟩ :=
    ModularCurve.exists_isIntegralQExp_smul_slash_of_mem_Gamma0 M (restrictForm hle f) hp γ hγ
  refine ⟨D, (D : ℂ) • DiamondLift.slashForm γ hγ f, p₁, hD, ?_, ?_⟩
  · rw [IsIntegralQExp] at hp₁ ⊢
    rw [hp₁, hf₁, coe_restrictForm, FunLike.coe_smul, DiamondLift.coe_slashForm,
      ModularForm.SL_slash]
  · rw [FunLike.coe_smul, DiamondLift.coe_slashForm, ModularForm.SL_slash]

/-- If `γ'` and `γd` differ by an element of `Γ_H(M)`, their slashes agree. The
`Γ_H(M)`-invariance of a `Γ_H(M)`-form, which the pin gets from
`A2HDIA.slashForm_slashForm`/`slashForm_of_mem`. -/
private theorem slash_eq_of_mul_inv_mem {k : ℤ}
    (f : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k) {γ γd : SL(2, ℤ)}
    (hmem : γ * γd⁻¹ ∈ CohCarrier.GammaH M H) :
    (⇑f : ℍ → ℂ) ∣[k] (γ : GL (Fin 2) ℝ) = (⇑f : ℍ → ℂ) ∣[k] (γd : GL (Fin 2) ℝ) := by
  have hfix : (⇑f : ℍ → ℂ) ∣[k] (((γ * γd⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ)) = ⇑f :=
    SlashInvariantFormClass.slash_action_eq f _
      (Subgroup.mem_map_of_mem (Matrix.SpecialLinearGroup.mapGL ℝ) hmem)
  have e : (γ : GL (Fin 2) ℝ)
      = ((γ * γd⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ) * (γd : GL (Fin 2) ℝ) := by
    conv_lhs => rw [← show γ * γd⁻¹ * γd = γ from inv_mul_cancel_right γ γd]
    simp only [map_mul]
  rw [e, SlashAction.slash_mul, hfix]

/-- The pin's `A2HDIA.mem_GammaH_of_upperLeft`. -/
private theorem mem_GammaH_of_upperLeft (γd : Gamma0 M) {d : (ZMod M)ˣ}
    (hγd : CohCarrier.gamma0Units M γd = d⁻¹) {γ' : SL(2, ℤ)} (hγ' : γ' ∈ Gamma0 M)
    (hd : ((γ' 0 0 : ℤ) : ZMod M) = (d : ZMod M)) :
    γ' * (γd : SL(2, ℤ))⁻¹ ∈ CohCarrier.GammaH M H := by
  rw [CohCarrier.mem_GammaH_iff]
  refine ⟨mul_mem hγ' (inv_mem γd.2), ?_⟩
  have hu : (CohCarrier.gamma0Units M ⟨γ', hγ'⟩)⁻¹ = d := Units.ext hd
  have hprod : (⟨γ' * (γd : SL(2, ℤ))⁻¹, mul_mem hγ' (inv_mem γd.2)⟩ : Gamma0 M)
      = ⟨γ', hγ'⟩ * γd⁻¹ := rfl
  rw [hprod, map_mul, map_inv, hγd, inv_inv, ← hu, mul_inv_cancel]
  exact one_mem H

-- The engine spells the field `qExpFunctionFieldC ℚ (Γ_H M H)`, the pin's
-- `xHFunctionField M H`; they are the same `def`/`abbrev` pair, and the pin's
-- lakefile compares types at `.all` transparency globally.
section Transparency

set_option backward.isDefEq.respectTransparency.types false

/-- The pin's `A2HDIA.exists_algEquiv_of_slashRational`, over the general-`Γ`
engine of `XH/DiamondLiftPrelude.lean`. The pin's conclusion is an `AlgEquiv`; the
engine's `sigma` is a `RingEquiv`, which is all its consumers use. -/
private theorem exists_ringEquiv_of_rationalSlash
    (hR : DiamondLift.RationalSlash (CohCarrier.GammaH M H) (Gamma0 M)) (d : (ZMod M)ˣ) :
    ∃ σ : qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)
        ≃+* qExpFunctionFieldC ℚ (CohCarrier.GammaH M H),
      ∀ (k : ℤ) (f g : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k)
        (pf pg : PowerSeries ℤ) (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg)
        (hg0 : intSeriesC ℚ pg ≠ 0) (γ : SL(2, ℤ)), γ ∈ Gamma0 M →
        ((γ 0 0 : ℤ) : ZMod M) = (d : ZMod M) →
        coeffMap (algebraMap ℚ ℂ)
              ((σ ⟨intSeriesC ℚ pf / intSeriesC ℚ pg,
                  div_mem_qExpFunctionFieldC f g hf hg hg0⟩ :
                qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) :
                LaurentSeries ℚ) *
            HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 (⇑g ∣[k] (γ : GL (Fin 2) ℝ))) =
          HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 (⇑f ∣[k] (γ : GL (Fin 2) ℝ))) := by
  obtain ⟨γd, hγd⟩ := CohCarrier.gamma0Units_surjective M d⁻¹
  refine ⟨DiamondLift.sigma hR (γd : SL(2, ℤ)) γd.2, ?_⟩
  intro k f g pf pg hf hg hg0 γ' hγ' hd
  have key : DiamondLift.toC
        (((DiamondLift.sigma hR (γd : SL(2, ℤ)) γd.2)
          ⟨intSeriesC ℚ pf / intSeriesC ℚ pg, div_mem_qExpFunctionFieldC f g hf hg hg0⟩ :
            qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) : LaurentSeries ℚ)
      = DiamondLift.qC ((⇑f : ℍ → ℂ) ∣[k] (γd : GL (Fin 2) ℝ))
        / DiamondLift.qC ((⇑g : ℍ → ℂ) ∣[k] (γd : GL (Fin 2) ℝ)) :=
    DiamondLift.toC_sigma_generator (Γ := CohCarrier.GammaH M H) (Δ := Gamma0 M)
      hR (γd : SL(2, ℤ)) γd.2 f g hf hg hg0
  have hδ := mem_GammaH_of_upperLeft M H γd hγd hγ' hd
  have hslash : ∀ (F : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k),
      (⇑F : ℍ → ℂ) ∣[k] (γ' : GL (Fin 2) ℝ) = (⇑F : ℍ → ℂ) ∣[k] (γd : GL (Fin 2) ℝ) :=
    fun F => slash_eq_of_mul_inv_mem M H F hδ
  have hgne : g ≠ 0 := fun h =>
    DiamondLift.qC_ne_zero_of_intSeriesC_ne_zero hg hg0 (by rw [h]; exact DiamondLift.qC_zero)
  have hne : DiamondLift.qC ((⇑g : ℍ → ℂ) ∣[k] (γd : GL (Fin 2) ℝ)) ≠ 0 := by
    rw [← DiamondLift.coe_slashForm (Γ := CohCarrier.GammaH M H) (Δ := Gamma0 M)
      (γ := (γd : SL(2, ℤ))) γd.2 g]
    rw [ne_eq, DiamondLift.qC_eq_zero_iff]
    exact DiamondLift.slashForm_ne_zero γd.2 hgne
  show DiamondLift.toC _ * DiamondLift.qC _ = DiamondLift.qC _
  rw [hslash f, hslash g, key, div_mul_cancel₀ _ hne]

/-- The pin's `A2HDIH.exists_isDiamondAutHBar`, over the engine's `σ₀` and the
base-change cover. -/
private theorem exists_isDiamondAutHBar (d : (ZMod M)ˣ) :
    ∃ σ : xHFunctionFieldBar M H ≃ₐ[AlgebraicClosure ℚ] xHFunctionFieldBar M H,
      IsDiamondAutHBar M H d σ := by
  obtain ⟨σ₀, hσ₀⟩ := exists_ringEquiv_of_rationalSlash M H (rationalSlash_GammaH M H) d
  obtain ⟨τ, hτ⟩ := ModularCurve.exists_algEquiv_laurentBaseChange_cover (AlgebraicClosure ℚ)
    (xHFunctionField M H) σ₀
  refine ⟨τ, ?_⟩
  intro k f g pf pg hf hg hg0 γ hγ hd
  refine ⟨(σ₀ ⟨intSeriesC ℚ pf / intSeriesC ℚ pg,
      div_mem_qExpFunctionFieldC f g hf hg hg0⟩ : xHFunctionField M H), SetLike.coe_mem _, ?_,
    hσ₀ k f g pf pg hf hg hg0 γ hγ hd⟩
  exact hτ ⟨intSeriesC ℚ pf / intSeriesC ℚ pg, div_mem_qExpFunctionFieldC f g hf hg hg0⟩

end Transparency

/-- The bundle of inputs for the `X_H(M)` Hecke operators (every prime `ℓ`) and the
diamond automorphisms (every `d ∈ (ZMod M)ˣ`): the Hecke half from
`XH/HeckeInputs.lean`, the diamond half from the general-`Γ` engine. -/
theorem heckeDiamondInputsHAll (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    HeckeDiamondInputsHAll M H :=
  ⟨fun ℓ hℓ => by
      haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
      exact HeckeInputsHAll.heckeInputsHAlong (AlgebraicClosure ℚ) M H ℓ,
    fun d => exists_isDiamondAutHBar M H d⟩

end ModularCurve

end
