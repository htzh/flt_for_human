/-
  The modulus of a continuous idèle-class character is a power of the idèle norm.

  `NumberField.TateGlobal.exists_norm_apply_eq_ideleNorm_rpow`: a continuous character
  `μ : (𝔸_F)ˣ →* ℂˣ` that is trivial on the principal idèles has
  `‖μ x‖ = ‖x‖ ^ σ` for a single real exponent `σ`.

  The proof writes `modulus μ : (𝔸_F)ˣ →* ℝ` for `x ↦ ‖μ x‖`. The modulus is trivial on
  the principal idèles (`modulus_principal`, from `IsIdeleClassChar`) and therefore on
  the compact quotient `𝔸_F^1 / F^×` of the norm-one idèles
  (`apply_eq_one_of_mem_normOneIdeles`: a compact range plus the semigroup power
  argument `pow_unbounded_of_one_lt`). The archimedean ray `ρ : ℝˣ →* (𝔸_F)ˣ` built from
  one infinite place `w` (`exists_ray`, through `exists_realEmbedding` and
  `archUnitHom w`) has `ideleNorm (ρ r) = |r| ^ n` with `n = w.mult > 0`, so every idèle
  is a norm-one idèle times some `ρ r`; on the ray the modulus is forced by continuity of
  the additive logarithm `rayLog` to be `r ↦ r ^ rayLog 1` (`apply_eq_rpow`). The same
  three facts hold for the idèle norm itself (`ideleNormHom`), and comparing the two
  gives the exponent `σ = rayLog ((modulus μ) ∘ ρ) 1 / n`.

  Transcribed from `P2M/Sol/S_NumberField_TateGlobal_exists_norm_apply_eq_ideleNorm_rpow.lean`
  (pinned `aa2d8b3`, 236 lines / 24 declarations); the statement is the one its wrapper
  `Theorems/Thm_NumberField_TateGlobal_exists_norm_apply_eq_ideleNorm_rpow.lean` declares,
  and the headline is declared at the wrapper's name. The pin's private helpers are kept
  private in the pin's `IdeleClassCharacterModule` namespace.

  Scaffolding dropped: `import P2M.Util`, the two `p2m_*` commands and the pin's
  `namespace P2MW.S_…` wrapper (its one inner namespace is kept at the root). The pin's
  whole `attribute [-instance] …` line is **not** carried over: it names mathlib `v4.30`
  instances mangled with `…_definitions` suffixes that do not exist in `v4.34.0`, and the
  proof elaborates without it (the same call and wording as
  `NumberTheory/RatIdele/ClassCharNorm.lean`'s header).

  Two groups of pin-private prelude are *not* re-proved because the port already has them
  as public mathematics at the same statements, and re-proving them here would be a
  duplicate declaration pair:
  * `continuous_archUnitHom` — the port's
    `NumberField.TateGlobal.FujisakiC3.continuous_archUnitHom`
    (`NumberField/TateGlobal/NormSection.lean`), and the `coe_archCentralUnit_eq` that
    only its proof used;
  * `ideleNorm_archUnitHom` — the port's `NumberField.TateGlobal.ideleNorm_archUnitHom`
    (`NumberField/TateGlobal/ArchNorm.lean`), which also discharges the pin's
    `distribHaarChar_eq_prod_norm_pow_mult_of_snd_eq_one` step.

  spec-pin: Theorems/Thm_NumberField_TateGlobal_exists_norm_apply_eq_ideleNorm_rpow.lean
  spec-pin: P2M/Sol/S_NumberField_TateGlobal_exists_norm_apply_eq_ideleNorm_rpow.lean   -- comparable copy
-/
import FLTForHuman.AutomorphicForm.Adelic.LsXi
import FLTForHuman.NumberTheory.AdelicHaar.PlaceMeasure
import FLTForHuman.NumberTheory.NumberField.IdeleClass.Vocab
import FLTForHuman.NumberTheory.NumberField.TateGlobal.Defs
import FLTForHuman.NumberTheory.NumberField.TateGlobal.NormSection
import FLTForHuman.NumberTheory.NumberField.TateGlobalCompactness

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain

namespace IdeleClassCharacterModule

private def expUnit (s : ℝ) : ℝˣ := Units.mk0 (Real.exp s) (Real.exp_ne_zero s)

private theorem coe_expUnit (s : ℝ) : ((expUnit s : ℝˣ) : ℝ) = Real.exp s := rfl

private theorem expUnit_zero : expUnit 0 = 1 :=
  Units.ext (by rw [coe_expUnit, Real.exp_zero, Units.val_one])

private theorem expUnit_add (s s' : ℝ) : expUnit (s + s') = expUnit s * expUnit s' :=
  Units.ext (by rw [Units.val_mul, coe_expUnit, coe_expUnit, coe_expUnit, Real.exp_add])

private theorem continuous_expUnit : Continuous expUnit := by
  refine Units.continuous_iff.2 ⟨Real.continuous_exp, ?_⟩
  simp only [expUnit, Units.val_inv_eq_inv_val, Units.val_mk0]
  exact Real.continuous_exp.inv₀ fun s => Real.exp_ne_zero s

private theorem eq_expUnit_log (r : ℝˣ) (hr : 0 < (r : ℝ)) : r = expUnit (Real.log r) :=
  Units.ext (by rw [coe_expUnit, Real.exp_log hr])

private def rayLog (g : ℝˣ →* ℝ) (hpos : ∀ r, 0 < g r) : ℝ →+ ℝ where
  toFun s := Real.log (g (expUnit s))
  map_zero' := by
    show Real.log (g (expUnit 0)) = 0
    rw [expUnit_zero, map_one, Real.log_one]
  map_add' s s' := by
    show Real.log (g (expUnit (s + s'))) = Real.log (g (expUnit s)) + Real.log (g (expUnit s'))
    rw [expUnit_add, map_mul]
    exact Real.log_mul (hpos _).ne' (hpos _).ne'

private theorem rayLog_apply (g : ℝˣ →* ℝ) (hpos : ∀ r, 0 < g r) (s : ℝ) :
    rayLog g hpos s = Real.log (g (expUnit s)) := rfl

private theorem continuous_rayLog (g : ℝˣ →* ℝ) (hpos : ∀ r, 0 < g r) (hg : Continuous g) :
    Continuous (rayLog g hpos) := by
  show Continuous fun s : ℝ => Real.log (g (expUnit s))
  exact (hg.comp continuous_expUnit).log fun s => (hpos _).ne'

private theorem apply_eq_rpow (g : ℝˣ →* ℝ) (hpos : ∀ r, 0 < g r) (hg : Continuous g) (r : ℝˣ)
    (hr : 0 < (r : ℝ)) : g r = (r : ℝ) ^ rayLog g hpos 1 := by
  have hlin : ∀ s : ℝ, rayLog g hpos s = s * rayLog g hpos 1 := fun s => by
    have h := map_real_smul (rayLog g hpos) (continuous_rayLog g hpos hg) s 1
    rwa [smul_eq_mul, smul_eq_mul, mul_one] at h
  rw [Real.rpow_def_of_pos hr, ← hlin, rayLog_apply, ← eq_expUnit_log r hr, Real.exp_log (hpos _)]

variable {K : Type} [Field K] [NumberField K]

private def modulus (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) : (AdeleRing (𝓞 K) K)ˣ →* ℝ :=
  (normHom : ℂ →*₀ ℝ).toMonoidHom.comp ((Units.coeHom ℂ).comp μ)

private theorem modulus_apply (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (x : (AdeleRing (𝓞 K) K)ˣ) :
    modulus μ x = ‖((μ x : ℂˣ) : ℂ)‖ := rfl

private theorem modulus_pos (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (x : (AdeleRing (𝓞 K) K)ˣ) :
    0 < modulus μ x := by
  rw [modulus_apply]
  exact norm_pos_iff.2 (Units.ne_zero (μ x))

private theorem continuous_modulus (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hc : Continuous μ) :
    Continuous (modulus μ) := by
  show Continuous fun x : (AdeleRing (𝓞 K) K)ˣ => ‖((μ x : ℂˣ) : ℂ)‖
  exact continuous_norm.comp (Units.continuous_val.comp hc)

private theorem modulus_principal (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (hμ : AutomorphicForm.IsIdeleClassChar (𝓞 K) K μ) (u : Kˣ) :
    modulus μ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) = 1 := by
  rw [modulus_apply, hμ u, Units.val_one, norm_one]

private def ideleNormHom : (AdeleRing (𝓞 K) K)ˣ →* ℝ where
  toFun := NumberField.TateGlobal.ideleNorm K
  map_one' := by
    have h : NumberField.TateGlobal.ideleNorm K (1 : (AdeleRing (𝓞 K) K)ˣ)
          * NumberField.TateGlobal.ideleNorm K 1
        = NumberField.TateGlobal.ideleNorm K (1 : (AdeleRing (𝓞 K) K)ˣ) * 1 := by
      rw [mul_one, ← NumberField.TateGlobal.ideleNorm_mul, one_mul]
    exact mul_left_cancel₀ (NumberField.TateGlobal.ideleNorm_pos _).ne' h
  map_mul' x y := NumberField.TateGlobal.ideleNorm_mul x y

private theorem ideleNormHom_apply (x : (AdeleRing (𝓞 K) K)ˣ) :
    ideleNormHom x = NumberField.TateGlobal.ideleNorm K x := rfl

private theorem apply_eq_one_of_mem_normOneIdeles (m : (AdeleRing (𝓞 K) K)ˣ →* ℝ) (hpos : ∀ x, 0 < m x)
    (hm : Continuous m)
    (hprin : ∀ u : Kˣ, m (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) = 1)
    (x : (AdeleRing (𝓞 K) K)ˣ) (hx : x ∈ NumberField.TateGlobal.normOneIdeles K) : m x = 1 := by
  set P : Subgroup (NumberField.TateGlobal.normOneIdeles K) :=
    (M4aHerbrand.principalIdeles (𝓞 K) K).subgroupOf (NumberField.TateGlobal.normOneIdeles K) with hP
  have : CompactSpace (↥(NumberField.TateGlobal.normOneIdeles K) ⧸ P) :=
    NumberField.TateGlobal.compactSpace_normOneIdeleClass K
  set m₁ : NumberField.TateGlobal.normOneIdeles K →* ℝ :=
    m.comp (NumberField.TateGlobal.normOneIdeles K).subtype with hm₁
  have hm₁c : Continuous m₁ := hm.comp continuous_subtype_val
  have hker : P ≤ m₁.ker := by
    intro h hh
    have hh' : (h : (AdeleRing (𝓞 K) K)ˣ) ∈ M4aHerbrand.principalIdeles (𝓞 K) K :=
      Subgroup.mem_subgroupOf.1 hh
    obtain ⟨u, hu⟩ := MonoidHom.mem_range.1 hh'
    rw [MonoidHom.mem_ker]
    show m (h : (AdeleRing (𝓞 K) K)ˣ) = 1
    rw [← hu]
    exact hprin u
  have hf : Continuous (QuotientGroup.lift P m₁ hker) :=
    (QuotientGroup.isQuotientMap_mk P).continuous_iff.2 (hm₁c.congr fun _ => rfl)
  obtain ⟨B, hB⟩ := (isCompact_range hf).bddAbove
  have hle : ∀ h : NumberField.TateGlobal.normOneIdeles K, m₁ h ≤ B := fun h =>
    hB (Set.mem_range_self (QuotientGroup.mk h : ↥(NumberField.TateGlobal.normOneIdeles K) ⧸ P))
  have key : ∀ h : NumberField.TateGlobal.normOneIdeles K, m₁ h ≤ 1 := fun h => by
    by_contra hgt
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt B (not_le.1 hgt)
    have h' := hle (h ^ n)
    rw [map_pow] at h'
    exact lt_irrefl B (lt_of_lt_of_le hn h')
  have h₁ := key ⟨x, hx⟩
  have h₂ := key (⟨x, hx⟩ : NumberField.TateGlobal.normOneIdeles K)⁻¹
  rw [map_inv] at h₂
  exact le_antisymm h₁ ((inv_le_one₀ (hpos x)).1 h₂)

omit [NumberField K] in
private theorem exists_realEmbedding (w : InfinitePlace K) :
    ∃ j : ℝ →+* w.Completion, Continuous j ∧ ∀ r : ℝ, ‖j r‖ = |r| := by
  rcases w.isReal_or_isComplex with hw | hw
  · refine ⟨(InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom, ?_, fun r => ?_⟩
    · exact (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).symm.continuous
    · rw [← Real.norm_eq_abs]
      exact (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).symm.isometry.norm_map_of_map_zero
        (map_zero (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm) r
  · refine ⟨(InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm.toRingHom.comp
        Complex.ofRealHom, ?_, fun r => ?_⟩
    · exact (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).symm.continuous.comp
        Complex.continuous_ofReal
    · have h := (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).symm.isometry.norm_map_of_map_zero
        (map_zero (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm) (r : ℂ)
      rw [Complex.norm_real, Real.norm_eq_abs] at h
      exact h

variable (K) in

private theorem exists_ray :
    ∃ (ρ : ℝˣ →* (AdeleRing (𝓞 K) K)ˣ) (n : ℕ), 0 < n ∧ Continuous ρ ∧
      ∀ r : ℝˣ, NumberField.TateGlobal.ideleNorm K (ρ r) = |(r : ℝ)| ^ n := by
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace K))
  obtain ⟨j, hjc, hjn⟩ := exists_realEmbedding w
  refine ⟨(NumberField.TateGlobal.archUnitHom w).comp (Units.map j.toMonoidHom), w.mult,
    InfinitePlace.mult_pos,
    (NumberField.TateGlobal.FujisakiC3.continuous_archUnitHom w).comp (hjc.units_map j.toMonoidHom),
    fun r => ?_⟩
  have h : ((Units.map j.toMonoidHom r : (w.Completion)ˣ) : w.Completion) = j r := rfl
  rw [MonoidHom.comp_apply, NumberField.TateGlobal.ideleNorm_archUnitHom, h, hjn]

end IdeleClassCharacterModule

open IdeleClassCharacterModule in

theorem NumberField.TateGlobal.exists_norm_apply_eq_ideleNorm_rpow
    (K : Type) [Field K] [NumberField K]
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : AutomorphicForm.IsIdeleClassChar (𝓞 K) K μ)
    (hc : Continuous μ) :
    ∃ σ : ℝ, ∀ x : (AdeleRing (𝓞 K) K)ˣ,
      ‖((μ x : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K x ^ σ := by
  have hpos : ∀ x, 0 < modulus μ x := modulus_pos μ
  have hmc : Continuous (modulus μ) := continuous_modulus μ hc
  obtain ⟨ρ, n, hn, hρc, hρN⟩ := exists_ray K
  have hgpos : ∀ r : ℝˣ, 0 < ((modulus μ).comp ρ) r := fun r => hpos (ρ r)
  have hgc : Continuous ((modulus μ).comp ρ) := hmc.comp hρc
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  refine ⟨(1 / (n : ℝ)) * rayLog ((modulus μ).comp ρ) hgpos 1, fun x => ?_⟩
  have hN : 0 < NumberField.TateGlobal.ideleNorm K x := NumberField.TateGlobal.ideleNorm_pos x
  obtain ⟨r, hr, hrv⟩ :
      ∃ r : ℝˣ, 0 < (r : ℝ) ∧ (r : ℝ) = NumberField.TateGlobal.ideleNorm K x ^ (1 / (n : ℝ)) :=
    ⟨Units.mk0 (NumberField.TateGlobal.ideleNorm K x ^ (1 / (n : ℝ)))
        (Real.rpow_pos_of_pos hN (1 / (n : ℝ))).ne',
      Real.rpow_pos_of_pos hN (1 / (n : ℝ)), rfl⟩

  have hNr : NumberField.TateGlobal.ideleNorm K (ρ r) = NumberField.TateGlobal.ideleNorm K x := by
    rw [hρN, abs_of_pos hr, hrv, ← Real.rpow_natCast, ← Real.rpow_mul hN.le, one_div,
      inv_mul_cancel₀ hn', Real.rpow_one]

  have hmem : x * (ρ r)⁻¹ ∈ NumberField.TateGlobal.normOneIdeles K := by
    rw [NumberField.TateGlobal.mem_normOneIdeles_iff, ← ideleNormHom_apply, map_mul, map_inv,
      ideleNormHom_apply, ideleNormHom_apply, hNr, mul_inv_cancel₀ hN.ne']
  have h₁ : modulus μ (x * (ρ r)⁻¹) = 1 :=
    apply_eq_one_of_mem_normOneIdeles (modulus μ) hpos hmc (modulus_principal μ hμ) _ hmem
  have h₂ : modulus μ (ρ r) = (r : ℝ) ^ rayLog ((modulus μ).comp ρ) hgpos 1 :=
    apply_eq_rpow _ hgpos hgc r hr
  have hx : modulus μ x = modulus μ (x * (ρ r)⁻¹) * modulus μ (ρ r) := by
    rw [← map_mul (modulus μ), inv_mul_cancel_right]
  rw [← modulus_apply, hx, h₁, one_mul, h₂, hrv, ← Real.rpow_mul hN.le]
