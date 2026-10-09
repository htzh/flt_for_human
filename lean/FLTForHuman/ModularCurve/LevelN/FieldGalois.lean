/-
  Phase A1 of `topics/modularCurve/WORKORDER-A-levelN-field.md`: the level-`N` function
  field `K` of `X(N)` and its `SL(2, ℤ)`-action.

  The four headlines are the pin's `Theorems/` wrappers verbatim; the proofs are the
  matching `P2M/Sol/S_ModularCurve_LevelN_*` files, adapted to mathlib `v4.34.0`.  The
  shared blocks (the `Good`/`Q` toolkit, the `ring N` action lemmas, `PB`) are imported
  from `LevelN/Prelude.lean`; everything else the pin declares is re-derived `private`
  in the pin's own sub-namespace, so this module's public surface is exactly the four
  headlines.

  FLT provenance, pinned `aa2d8b3`:
  * `S_ModularCurve_LevelN_isDomain_ring.lean:11-27`
  * `S_ModularCurve_LevelN_slash_eq_self_of_mem_Gamma_of_mul_eq.lean:24-258`
  * `S_ModularCurve_LevelN_exists_monoidHom_algEquiv_fixedField_eq_adjoin.lean:24-472`
  * `S_ModularCurve_LevelN_exists_algHom_laurentSeries_qExpansion.lean:309-602`
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_LevelN_exists_monoidHom_algEquiv_fixedField_eq_adjoin.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_LevelN_exists_algHom_laurentSeries_qExpansion.lean

  Drift: `Pi.algHom` (used inside the prelude's `precomp`) and
  `AlgEquiv.coe_algHom_injective` / `Set.mem_setOf_eq` are deprecated aliases in
  `v4.34.0`.  The pin's `set_option linter.unusedSectionVars false` /
  `linter.unusedVariables false` and its local `set_option maxHeartbeats` /
  `synthInstance.maxHeartbeats` bumps are not transcribed; the four declarations whose
  `[NeZero N]` the linter would flag carry an explicit `omit [NeZero N] in`, and the
  pin's `haveI`s that the style linter rejects are plain `have`s (their class is
  `Prop`-valued, so instance search still finds them).
-/
import FLTForHuman.ModularCurve.LevelN.Prelude
import FLTForHuman.ModularCurve.JqIntegralRatios
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
import Mathlib.RingTheory.HahnSeries.PowerSeries
import Mathlib.RingTheory.PowerSeries.Order

set_option autoImplicit false

noncomputable section

open UpperHalfPlane Filter Topology Function

open scoped MatrixGroups Manifold Real ModularForm

namespace ModularCurve

namespace LevelN

/-- Pin `ModularCurve.LevelN.isDomain_ring` (`S_..._isDomain_ring.lean:11`), at the
wrapper's statement. -/
theorem isDomain_ring (M : ℕ) [NeZero M] : IsDomain (ModularCurve.LevelN.ring M) := by
  have hpkg := WLight.levelN_structure_package M PeriodPair.ofTau
    (fun τ => ⟨PeriodPair.ofTau_ω₁ τ, PeriodPair.ofTau_ω₂ τ⟩)
    (ModularCurve.LevelN.wp M) (fun v τ => rfl)
    (ModularCurve.LevelN.fricke M) (fun v τ => rfl)
    ModularCurve.LevelN.jAnalytic (fun τ => rfl)
  obtain ⟨-, -, -, -, -, hdom⟩ := hpkg
  have hNZ : NoZeroDivisors (ModularCurve.LevelN.ring M) := ⟨fun {a b} h => by
    have h' := hdom (a : UpperHalfPlane → ℂ) (b : UpperHalfPlane → ℂ) a.2 b.2
      (by simpa using congrArg Subtype.val h)
    rcases h' with ha | hb
    · left; exact Subtype.ext ha
    · right; exact Subtype.ext hb⟩
  exact NoZeroDivisors.to_isDomain _

namespace WeightTwo

variable (N : ℕ) [NeZero N]










private theorem apply_smul_of_mem {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma N) {F : ℍ → ℂ}
    (hF : F ∈ ring N) (τ : ℍ) : F (γ • τ) = F τ := by
  have hle : ring N ≤ AlgHom.equalizer (precomp γ) (AlgHom.id ℂ (ℍ → ℂ)) := by
    rw [ring, Algebra.adjoin_le_iff]
    intro G hG
    rw [SetLike.mem_coe, AlgHom.mem_equalizer, AlgHom.id_apply]
    funext τ
    rw [precomp_apply]
    rcases hG with rfl | ⟨v, hv, rfl⟩
    · exact jAnalytic_smul γ τ
    · exact fricke_smul_of_mem N v hγ τ
  have := hle hF
  rw [AlgHom.mem_equalizer, AlgHom.id_apply] at this
  exact congrFun this τ
private def 𝕌 : Set ℂ := {z : ℂ | 0 < z.im}
private theorem isOpen_𝕌 : IsOpen 𝕌 := isOpen_upperHalfPlaneSet
private theorem isPreconnected_𝕌 : IsPreconnected 𝕌 := (convex_halfSpace_im_gt 0).isPreconnected
private theorem coe_mem_𝕌 (τ : ℍ) : (τ : ℂ) ∈ 𝕌 := τ.im_pos
private def up (F : ℍ → ℂ) : ℂ → ℂ := F ∘ ofComplex
private theorem up_apply_coe (F : ℍ → ℂ) (τ : ℍ) : up F τ = F τ := by
  simp [up, ofComplex_apply]
private theorem analyticOnNhd_up_of_mdifferentiable {F : ℍ → ℂ} (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) :
    AnalyticOnNhd ℂ (up F) 𝕌 := by
  intro z hz
  have hd : DifferentiableOn ℂ (up F) 𝕌 := UpperHalfPlane.mdifferentiable_iff.mp hF
  exact hd.analyticAt (isOpen_𝕌.mem_nhds hz)
private theorem analyticOnNhd_up {F : ℍ → ℂ} (hF : F ∈ ring N) : AnalyticOnNhd ℂ (up F) 𝕌 :=
  analyticOnNhd_up_of_mdifferentiable (mdifferentiable_of_mem N hF)
private theorem differentiableAt_up {F : ℍ → ℂ} (hF : F ∈ ring N) (τ : ℍ) :
    DifferentiableAt ℂ (up F) τ :=
  (analyticOnNhd_up N hF τ (coe_mem_𝕌 τ)).differentiableAt
private theorem up_eq_zero_iff (F : ℍ → ℂ) : (∀ z ∈ 𝕌, up F z = 0) ↔ F = 0 := by
  constructor
  · intro h
    funext τ
    simpa [up_apply_coe] using h τ (coe_mem_𝕌 τ)
  · rintro rfl z _
    rfl
private theorem eventually_ne_zero {F : ℍ → ℂ} (hF : F ∈ ring N) (hF0 : F ≠ 0) (τ : ℍ) :
    ∀ᶠ z in 𝓝[≠] (τ : ℂ), up F z ≠ 0 := by
  rcases (analyticOnNhd_up N hF τ (coe_mem_𝕌 τ)).eventually_eq_zero_or_eventually_ne_zero
    with h | h
  · exfalso
    apply hF0
    rw [← up_eq_zero_iff]
    intro z hz
    exact (analyticOnNhd_up N hF).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_𝕌 (coe_mem_𝕌 τ) h hz
  · exact h
private theorem eq_zero_of_mul_eq_zero {G : ℍ → ℂ} (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G) {p : ℍ → ℂ}
    (hp : p ∈ ring N) (hp0 : p ≠ 0) (h : ∀ τ : ℍ, p τ ≠ 0 → G τ = 0) : G = 0 := by
  funext τ
  have hcont : ContinuousAt (up G) τ :=
    (analyticOnNhd_up_of_mdifferentiable hG τ (coe_mem_𝕌 τ)).continuousAt
  have hev : ∀ᶠ z in 𝓝[≠] (τ : ℂ), up G z = 0 := by
    filter_upwards [eventually_ne_zero N hp hp0 τ,
      mem_nhdsWithin_of_mem_nhds (isOpen_𝕌.mem_nhds (coe_mem_𝕌 τ))] with z hz hzU
    have hz' : p ⟨z, hzU⟩ ≠ 0 := by
      simpa [up, ofComplex_apply_of_im_pos hzU] using hz
    have := h ⟨z, hzU⟩ hz'
    simpa [up, ofComplex_apply_of_im_pos hzU] using this
  have h1 : Tendsto (up G) (𝓝[≠] (τ : ℂ)) (𝓝 (up G τ)) := hcont.tendsto.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (up G) (𝓝[≠] (τ : ℂ)) (𝓝 0) :=
    tendsto_const_nhds.congr' (hev.mono fun z hz => hz.symm)
  have := tendsto_nhds_unique h1 h2
  rwa [up_apply_coe] at this
private def moeb (g : SL(2, ℤ)) (z : ℂ) : ℂ := ((g • ofComplex z : ℍ) : ℂ)
private theorem moeb_coe (g : SL(2, ℤ)) (τ : ℍ) : moeb g τ = ((g • τ : ℍ) : ℂ) := by
  simp [moeb, ofComplex_apply]
private theorem hasDerivAt_moeb (γ : SL(2, ℤ)) (τ : ℍ) :
    HasDerivAt (moeb γ) (denom (Matrix.SpecialLinearGroup.mapGL ℝ γ) ↑τ ^ (-2 : ℤ)) ↑τ := by
  set G : GL (Fin 2) ℝ := Matrix.SpecialLinearGroup.mapGL ℝ γ with hG
  have hdet : (G : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply, hG, Matrix.SpecialLinearGroup.det_mapGL,
      Units.val_one]
  have hpos : (0:ℝ) < (G : Matrix (Fin 2) (Fin 2) ℝ).det := by rw [hdet]; norm_num
  have h1 := (UpperHalfPlane.hasStrictDerivAt_smul hpos τ).hasDerivAt
  have h2 : (fun z : ℂ => ((G • ofComplex z : ℍ) : ℂ)) = moeb γ := by
    funext z
    rw [moeb, MulAction.compHom_smul_def]
  rw [h2] at h1
  (convert h1 using 1; try rfl)
  rw [hdet]
  push_cast
  rw [zpow_neg, one_div]
  norm_cast
private theorem deriv_up_smul {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma N) {c : ℍ → ℂ}
    (hc : c ∈ ring N) (τ : ℍ) :
    deriv (up c) ↑(γ • τ) * denom (Matrix.SpecialLinearGroup.mapGL ℝ γ) ↑τ ^ (-2 : ℤ) =
      deriv (up c) τ := by
  have hinv : up c ∘ moeb γ = up c := by
    funext z
    simp only [comp_apply, up, moeb, ofComplex_apply]
    exact apply_smul_of_mem N hγ hc _
  have h1 : HasDerivAt (up c ∘ moeb γ)
      (deriv (up c) (moeb γ τ) * denom (Matrix.SpecialLinearGroup.mapGL ℝ γ) ↑τ ^ (-2 : ℤ)) τ := by
    refine HasDerivAt.comp (τ : ℂ) ?_ (hasDerivAt_moeb γ τ)
    rw [moeb_coe]
    exact (differentiableAt_up N hc (γ • τ)).hasDerivAt
  rw [hinv] at h1
  rw [← moeb_coe]
  exact h1.deriv.symm
private theorem slash_two_apply (f : ℍ → ℂ) (γ : SL(2, ℤ)) (τ : ℍ) :
    (f ∣[(2 : ℤ)] γ) τ =
      f (γ • τ) * denom (Matrix.SpecialLinearGroup.mapGL ℝ γ) ↑τ ^ (-2 : ℤ) :=
  ModularForm.SL_slash_apply f γ τ
private theorem slash_apply_eq_of_ne {F : ℍ → ℂ} {a b c e : ℍ → ℂ} (ha : a ∈ ring N) (hb : b ∈ ring N)
    (hc : c ∈ ring N) (he : e ∈ ring N)
    (h : ∀ τ : ℍ, F τ * b τ * e τ ^ 2 =
      a τ * (e τ * deriv (c ∘ ofComplex) τ - c τ * deriv (e ∘ ofComplex) τ))
    {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma N) (τ : ℍ) (hbe : b τ * e τ ≠ 0) :
    (F ∣[(2 : ℤ)] γ) τ = F τ := by
  set D : ℂ := denom (Matrix.SpecialLinearGroup.mapGL ℝ γ) ↑τ ^ (-2 : ℤ) with hD
  have hD0 : D ≠ 0 := zpow_ne_zero _ (denom_ne_zero _ _)
  have h1 := h (γ • τ)
  rw [apply_smul_of_mem N hγ ha, apply_smul_of_mem N hγ hb, apply_smul_of_mem N hγ hc,
    apply_smul_of_mem N hγ he] at h1
  have hc' : deriv (c ∘ ofComplex) ↑(γ • τ) = deriv (c ∘ ofComplex) τ * D⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq₀ hD0]
    exact deriv_up_smul N hγ hc τ
  have he' : deriv (e ∘ ofComplex) ↑(γ • τ) = deriv (e ∘ ofComplex) τ * D⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq₀ hD0]
    exact deriv_up_smul N hγ he τ
  rw [hc', he'] at h1
  have h2 := h τ
  rw [slash_two_apply]

  have h3 : F (γ • τ) * (b τ * e τ ^ 2) = (F τ * D⁻¹) * (b τ * e τ ^ 2) := by
    calc F (γ • τ) * (b τ * e τ ^ 2) = F (γ • τ) * b τ * e τ ^ 2 := by ring
      _ = a τ * (e τ * (deriv (c ∘ ofComplex) τ * D⁻¹) - c τ * (deriv (e ∘ ofComplex) τ * D⁻¹)) := h1
      _ = (a τ * (e τ * deriv (c ∘ ofComplex) τ - c τ * deriv (e ∘ ofComplex) τ)) * D⁻¹ := by ring
      _ = (F τ * b τ * e τ ^ 2) * D⁻¹ := by rw [h2]
      _ = (F τ * D⁻¹) * (b τ * e τ ^ 2) := by ring
  have hbe2 : b τ * e τ ^ 2 ≠ 0 := by
    have hb0 : b τ ≠ 0 := left_ne_zero_of_mul hbe
    have he0 : e τ ≠ 0 := right_ne_zero_of_mul hbe
    exact mul_ne_zero hb0 (pow_ne_zero 2 he0)
  have h4 : F (γ • τ) = F τ * D⁻¹ := mul_right_cancel₀ hbe2 h3
  rw [h4, mul_assoc, inv_mul_cancel₀ hD0, mul_one]
private theorem slash_eq_self {F : ℍ → ℂ} (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) {a b c e : ℍ → ℂ}
    (ha : a ∈ ring N) (hb : b ∈ ring N) (hc : c ∈ ring N) (he : e ∈ ring N) (hb0 : b ≠ 0)
    (he0 : e ≠ 0)
    (h : ∀ τ : ℍ, F τ * b τ * e τ ^ 2 =
      a τ * (e τ * deriv (c ∘ ofComplex) τ - c τ * deriv (e ∘ ofComplex) τ))
    {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma N) :
    F ∣[(2 : ℤ)] γ = F := by
  have hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (F ∣[(2 : ℤ)] γ - F) := (hF.slash 2 _).sub hF
  have hp : b * e ∈ ring N := (ring N).mul_mem hb he
  have hp0 : b * e ≠ 0 := fun h0 =>
    (eq_zero_or_eq_zero_of_mul_eq_zero N hb he h0).elim hb0 he0
  have := eq_zero_of_mul_eq_zero N hG hp hp0 (fun τ hτ => by
    rw [Pi.sub_apply, slash_apply_eq_of_ne N ha hb hc he h hγ τ hτ, sub_self])
  exact sub_eq_zero.mp this
end WeightTwo

/-- Pin `ModularCurve.LevelN.slash_eq_self_of_mem_Gamma_of_mul_eq`
(`S_..._slash_eq_self_of_mem_Gamma_of_mul_eq.lean:248`), at the wrapper's statement. -/
theorem slash_eq_self_of_mem_Gamma_of_mul_eq (N : ℕ) [NeZero N]
    (F : UpperHalfPlane → ℂ) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F)
    (a b c e : UpperHalfPlane → ℂ) (ha : a ∈ ModularCurve.LevelN.ring N)
    (hb : b ∈ ModularCurve.LevelN.ring N) (hc : c ∈ ModularCurve.LevelN.ring N)
    (he : e ∈ ModularCurve.LevelN.ring N) (hb0 : b ≠ 0) (he0 : e ≠ 0)
    (h : ∀ τ : UpperHalfPlane, F τ * b τ * e τ ^ 2 =
      a τ * (e τ * deriv (c ∘ UpperHalfPlane.ofComplex) τ -
        c τ * deriv (e ∘ UpperHalfPlane.ofComplex) τ))
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma N) :
    F ∣[(2 : ℤ)] γ = F :=
  WeightTwo.slash_eq_self N hF ha hb hc he hb0 he0 h hγ

namespace GaloisStructure

variable (N : ℕ)

private abbrev Gpm : Subgroup SL(2, ℤ) := CongruenceSubgroup.Gamma N ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))
scoped instance zpowers_neg_one_normal : (Subgroup.zpowers (-1 : SL(2, ℤ))).Normal :=
  ⟨fun n hn g => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    have hc : Commute g ((-1 : SL(2, ℤ)) ^ k) := (Commute.neg_one_right g).zpow_right k
    rw [hc.eq, mul_inv_cancel_right]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) k⟩
private theorem neg_one_mem_Gpm : (-1 : SL(2, ℤ)) ∈ Gpm N :=
  Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
private theorem mem_Gpm_of_mem {g : SL(2, ℤ)} (hg : g ∈ CongruenceSubgroup.Gamma N) : g ∈ Gpm N :=
  Subgroup.mem_sup_left hg
private theorem neg_mem_Gpm {g : SL(2, ℤ)} (hg : g ∈ Gpm N) : -g ∈ Gpm N := by
  rw [← neg_one_mul]; exact (Gpm N).mul_mem (neg_one_mem_Gpm N) hg
private theorem exists_of_mem_Gpm {g : SL(2, ℤ)} (hg : g ∈ Gpm N) :
    ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma N ∧ (g = γ ∨ g = -γ) := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hg
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  refine ⟨y, hy, ?_⟩
  have h2 : ((-1 : SL(2, ℤ)) ^ (2 : ℤ)) = 1 := by rw [zpow_two]; simp
  rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · left
    rw [← two_mul, zpow_mul, h2, one_zpow, mul_one]
  · right
    rw [zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one, mul_neg_one]
private theorem mem_Gpm_iff (g : SL(2, ℤ)) :
    g ∈ Gpm N ↔ g ∈ CongruenceSubgroup.Gamma N ∨ -g ∈ CongruenceSubgroup.Gamma N := by
  constructor
  · intro hg
    obtain ⟨γ, hγ, h | h⟩ := exists_of_mem_Gpm N hg
    · left; rwa [h]
    · right; rw [h, neg_neg]; exact hγ
  · rintro (h | h)
    · exact mem_Gpm_of_mem N h
    · have := neg_mem_Gpm N (mem_Gpm_of_mem N h)
      rwa [neg_neg] at this
scoped instance Gpm_finiteIndex [NeZero N] : (Gpm N).FiniteIndex :=
  Subgroup.finiteIndex_of_le (le_sup_left : CongruenceSubgroup.Gamma N ≤ Gpm N)

variable [NeZero N]

private theorem fixer_eq :
    {γ : SL(2, ℤ) | ∀ v : Fin 2 → ZMod N, v ≠ 0 →
        fricke N (Matrix.vecMul v (redMat N γ)) = fricke N v} =
      {γ : SL(2, ℤ) | γ ∈ CongruenceSubgroup.Gamma N ∨ -γ ∈ CongruenceSubgroup.Gamma N} := by
  have h := WLight.levelN_structure_package N PeriodPair.ofTau (fun _ => ⟨rfl, rfl⟩) (wp N)
    (fun v τ => rfl) (fricke N) (fun v τ => rfl) jAnalytic (fun τ => rfl)
  exact h.1
private theorem invariant_fraction (a b : ℍ → ℂ) (ha : a ∈ ring N) (hb : b ∈ ring N) (hb0 : b ≠ 0)
    (hinv : ∀ γ : SL(2, ℤ), a * (b ∘ (γ • ·)) = (a ∘ (γ • ·)) * b) :
    ∃ p q : Polynomial ℂ, q ≠ 0 ∧
      a * (fun τ => q.eval (jAnalytic τ)) = b * (fun τ => p.eval (jAnalytic τ)) := by
  have h := WLight.levelN_structure_package N PeriodPair.ofTau (fun _ => ⟨rfl, rfl⟩) (wp N)
    (fun v τ => rfl) (fricke N) (fun v τ => rfl) jAnalytic (fun τ => rfl)
  exact h.2.1 a b ha hb hb0 hinv
omit [NeZero N] in

private theorem eq_zero_of_eval_jAnalytic (P : Polynomial ℂ) (hP : ∀ τ : ℍ, P.eval (jAnalytic τ) = 0) :
    P = 0 := by
  have h := WLight.levelN_structure_package 1 PeriodPair.ofTau (fun _ => ⟨rfl, rfl⟩) (wp 1)
    (fun v τ => rfl) (fricke 1) (fun v τ => rfl) jAnalytic (fun τ => rfl)
  exact h.2.2.2.1 P hP
private theorem fricke_smul (v : Fin 2 → ZMod N) (γ : SL(2, ℤ)) (τ : ℍ) :
    fricke N v (γ • τ) = fricke N (Matrix.vecMul v (redMat N γ)) τ :=
  (WLight.frickeFunction_modularity_package N PeriodPair.ofTau (fun _ => ⟨rfl, rfl⟩)).1 v γ τ


omit [NeZero N] in

private theorem vecMul_ne_zero {v : Fin 2 → ZMod N} (hv : v ≠ 0) (γ : SL(2, ℤ)) :
    Matrix.vecMul v (redMat N γ) ≠ 0 := by
  intro h
  apply hv
  have hdet : (redMat N γ).det = 1 := by
    have := congrArg ((↑) : ℤ → ZMod N) γ.2
    rw [Int.cast_one] at this
    rw [← this, redMat]
    exact (RingHom.map_det (Int.castRingHom (ZMod N)) _).symm
  have hunit : IsUnit (redMat N γ).det := by rw [hdet]; exact isUnit_one
  have := congrArg (fun w => Matrix.vecMul w (redMat N γ)⁻¹) h
  simp only [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hunit, Matrix.vecMul_one,
    Matrix.zero_vecMul] at this
  exact this



private theorem precomp_mem (g : SL(2, ℤ)) {F : ℍ → ℂ} (hF : F ∈ ring N) : precomp g F ∈ ring N := by
  have hle : (ring N).map (precomp g) ≤ ring N := by
    rw [ring, AlgHom.map_adjoin, Algebra.adjoin_le_iff]
    rintro _ ⟨G, hG, rfl⟩
    rcases hG with rfl | ⟨v, hv, rfl⟩
    · have : precomp g jAnalytic = jAnalytic := funext fun τ => jAnalytic_smul g τ
      rw [this]
      exact jAnalytic_mem N
    · have : precomp g (fricke N v) = fricke N (Matrix.vecMul v (redMat N g)) :=
        funext fun τ => fricke_smul N v g τ
      rw [this]
      exact fricke_mem N (vecMul_ne_zero N hv g)
  exact hle ⟨F, hF, rfl⟩
set_option linter.unusedSectionVars false in
private theorem comp_smul_mem (g : SL(2, ℤ)) {F : ℍ → ℂ} (hF : F ∈ ring N) :
    (fun τ : ℍ => F (g • τ)) ∈ ring N :=
  precomp_mem N g hF
private def res (g : SL(2, ℤ)) : ring N →ₐ[ℂ] ring N :=
  ((precomp g).comp (ring N).val).codRestrict (ring N) fun F => precomp_mem N g F.2
set_option linter.unusedSectionVars false in
@[scoped simp]
private theorem coe_res_apply (g : SL(2, ℤ)) (F : ring N) (τ : ℍ) :
    ((res N g F : ring N) : ℍ → ℂ) τ = (F : ℍ → ℂ) (g • τ) := rfl
set_option linter.unusedSectionVars false in
private theorem res_comp (g h : SL(2, ℤ)) : (res N g).comp (res N h) = res N (h * g) := by
  ext F τ
  simp [mul_smul]
set_option linter.unusedSectionVars false in
private theorem res_one : res N 1 = AlgHom.id ℂ (ring N) := by
  ext F τ
  simp
private def ρ (γ : SL(2, ℤ)) : ring N ≃ₐ[ℂ] ring N :=
  AlgEquiv.ofAlgHom (res N γ⁻¹) (res N γ)
    (by rw [res_comp, mul_inv_cancel, res_one])
    (by rw [res_comp, inv_mul_cancel, res_one])
@[scoped simp]
private theorem coe_ρ_apply (γ : SL(2, ℤ)) (F : ring N) (τ : ℍ) :
    ((ρ N γ F : ring N) : ℍ → ℂ) τ = (F : ℍ → ℂ) (γ⁻¹ • τ) := rfl
private def ρHom : SL(2, ℤ) →* (ring N ≃ₐ[ℂ] ring N) where
  toFun := ρ N
  map_one' := by
    ext F τ
    simp
  map_mul' γ δ := by
    ext F τ
    simp [mul_smul]
@[scoped simp]
private theorem coe_ρHom_apply (γ : SL(2, ℤ)) (F : ring N) (τ : ℍ) :
    ((ρHom N γ F : ring N) : ℍ → ℂ) τ = (F : ℍ → ℂ) (γ⁻¹ • τ) := rfl

section FractionField

variable (K : Type*) [Field K] [Algebra ℂ K] [Algebra (ring N) K] [IsScalarTower ℂ (ring N) K]
  [IsFractionRing (ring N) K]
private def σHom : SL(2, ℤ) →* (K ≃ₐ[ℂ] K) :=
  (IsFractionRing.fieldEquivOfAlgEquivHom ℂ K).comp (ρHom N)
private theorem σHom_algebraMap (γ : SL(2, ℤ)) (F : ring N) :
    σHom N K γ (algebraMap (ring N) K F) = algebraMap (ring N) K (ρHom N γ F) := by
  simp [σHom]
private theorem σHom_algebraMap' (γ : SL(2, ℤ)) (F : ℍ → ℂ) (hF : F ∈ ring N) :
    σHom N K γ (algebraMap (ring N) K ⟨F, hF⟩) =
      algebraMap (ring N) K ⟨fun τ : ℍ => F (γ⁻¹ • τ), comp_smul_mem N γ⁻¹ hF⟩ := by
  rw [σHom_algebraMap]
  rfl
private theorem ker_σHom : (σHom N K).ker = (ρHom N).ker := by
  rw [σHom, ← MonoidHom.comap_ker,
    (MonoidHom.ker_eq_bot_iff _).mpr (IsFractionRing.fieldEquivOfAlgEquivHom_injective ℂ (ring N) ℂ K),
    MonoidHom.comap_bot]
omit [NeZero N] in

private theorem algHom_eq_id_of_forall {φ : ring N →ₐ[ℂ] ring N}
    (h : ∀ (G : ℍ → ℂ) (hG : G ∈ generators N), φ ⟨G, Algebra.subset_adjoin hG⟩ =
      ⟨G, Algebra.subset_adjoin hG⟩) : φ = AlgHom.id ℂ (ring N) := by
  ext1 F
  obtain ⟨F, hF⟩ := F
  change F ∈ Algebra.adjoin ℂ (generators N) at hF
  induction hF using Algebra.adjoin_induction with
  | mem x hx => exact h x hx
  | algebraMap c =>
      have : (⟨algebraMap ℂ (ℍ → ℂ) c, _⟩ : ring N) = algebraMap ℂ (ring N) c := rfl
      rw [this, AlgHom.commutes]; rfl
  | add x y hx hy ihx ihy =>
      have : (⟨x + y, _⟩ : ring N) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
      rw [this, map_add, ihx, ihy]; rfl
  | mul x y hx hy ihx ihy =>
      have : (⟨x * y, _⟩ : ring N) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
      rw [this, map_mul, ihx, ihy]; rfl
private theorem ρHom_eq_one_iff (γ : SL(2, ℤ)) :
    ρHom N γ = 1 ↔
      ∀ v : Fin 2 → ZMod N, v ≠ 0 → fricke N (Matrix.vecMul v (redMat N γ⁻¹)) = fricke N v := by
  constructor
  · intro h v hv
    have hF := congrArg (fun e : ring N ≃ₐ[ℂ] ring N => ((e ⟨fricke N v, fricke_mem N hv⟩ : ring N) : ℍ → ℂ)) h
    funext τ
    have := congrFun hF τ
    change fricke N v (γ⁻¹ • τ) = fricke N v τ at this
    rwa [fricke_smul] at this
  · intro h
    apply AlgEquiv.coe_toAlgHom_injective
    change (res N γ⁻¹ : ring N →ₐ[ℂ] ring N) = AlgHom.id ℂ (ring N)
    refine algHom_eq_id_of_forall N fun G hG => ?_
    apply Subtype.ext
    funext τ
    change G (γ⁻¹ • τ) = G τ
    rcases hG with rfl | ⟨v, hv, rfl⟩
    · exact jAnalytic_smul γ⁻¹ τ
    · rw [fricke_smul, h v hv]
private theorem ker_ρHom : (ρHom N).ker = Gpm N := by
  ext γ
  rw [MonoidHom.mem_ker, ρHom_eq_one_iff]
  have hset := fixer_eq N
  have hmem : γ⁻¹ ∈ {γ : SL(2, ℤ) | ∀ v : Fin 2 → ZMod N, v ≠ 0 →
      fricke N (Matrix.vecMul v (redMat N γ)) = fricke N v} ↔
      γ⁻¹ ∈ {γ : SL(2, ℤ) | γ ∈ CongruenceSubgroup.Gamma N ∨ -γ ∈ CongruenceSubgroup.Gamma N} := by
    rw [hset]
  simp only [Set.mem_ofPred_eq] at hmem
  rw [hmem, ← mem_Gpm_iff, inv_mem_iff]
private theorem ker_σHom_eq : (σHom N K).ker = Gpm N := by
  rw [ker_σHom, ker_ρHom]
private abbrev jK : K := algebraMap (ring N) K (jGen N)
private theorem ρHom_jGen (γ : SL(2, ℤ)) : ρHom N γ (jGen N) = jGen N := by
  apply Subtype.ext
  funext τ
  change jAnalytic (γ⁻¹ • τ) = jAnalytic τ
  exact jAnalytic_smul γ⁻¹ τ
private theorem σHom_jK (γ : SL(2, ℤ)) : σHom N K γ (jK N K) = jK N K := by
  change σHom N K γ (algebraMap (ring N) K (jGen N)) = algebraMap (ring N) K (jGen N)
  rw [σHom_algebraMap, ρHom_jGen]
set_option linter.unusedSectionVars false in
private theorem coe_aeval_jGen (p : Polynomial ℂ) (τ : ℍ) :
    ((Polynomial.aeval (jGen N) p : ring N) : ℍ → ℂ) τ = p.eval (jAnalytic τ) := by
  have h1 : ((Polynomial.aeval (jGen N) p : ring N) : ℍ → ℂ) =
      Polynomial.aeval (jAnalytic) p := by
    rw [← coe_jGen N, ← Subalgebra.coe_val, ← Polynomial.aeval_algHom_apply]
  rw [h1]
  have h2 : (Polynomial.aeval jAnalytic p) τ =
      Pi.evalAlgHom ℂ (fun _ : ℍ => ℂ) τ (Polynomial.aeval jAnalytic p) := rfl
  rw [h2, ← Polynomial.aeval_algHom_apply, Polynomial.coe_aeval_eq_eval]
  rfl
set_option linter.unusedSectionVars false in
private theorem transcendental_jK : Transcendental ℂ (jK N K) := by
  rw [transcendental_iff]
  intro P hP
  apply eq_zero_of_eval_jAnalytic P
  intro τ
  change Polynomial.aeval (algebraMap (ring N) K (jGen N)) P = 0 at hP
  rw [Polynomial.aeval_algebraMap_apply,
    map_eq_zero_iff _ (IsFractionRing.injective (ring N) K)] at hP
  rw [← coe_aeval_jGen N P τ, hP]
  rfl
private theorem aeval_jK_ne_zero {q : Polynomial ℂ} (hq : q ≠ 0) : Polynomial.aeval (jK N K) q ≠ 0 :=
  fun h => hq ((transcendental_iff.mp (transcendental_jK N K)) q h)
private theorem fixedField_eq :
    IntermediateField.fixedField (σHom N K).range =
      IntermediateField.adjoin ℂ ({jK N K} : Set K) := by
  apply le_antisymm
  ·
    intro x hx
    rw [IntermediateField.mem_fixedField_iff] at hx
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := ring N) x
    have hb0 : (b : ℍ → ℂ) ≠ 0 := by
      intro h
      have : b = 0 := Subtype.ext h
      rw [this] at hb
      exact zero_notMem_nonZeroDivisors hb
    have hbK : algebraMap (ring N) K b ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb

    have hinv : ∀ γ : SL(2, ℤ), (a : ℍ → ℂ) * ((b : ℍ → ℂ) ∘ (γ • ·)) =
        ((a : ℍ → ℂ) ∘ (γ • ·)) * (b : ℍ → ℂ) := by
      intro γ
      have h := hx (σHom N K γ⁻¹) ⟨γ⁻¹, rfl⟩
      rw [map_div₀, σHom_algebraMap, σHom_algebraMap, div_eq_div_iff _ hbK] at h
      · rw [← map_mul, ← map_mul] at h
        have h' := IsFractionRing.injective (ring N) K h
        have h'' := congrArg (fun F : ring N => (F : ℍ → ℂ)) h'
        simp only [Subalgebra.coe_mul] at h''

        funext τ
        have := congrFun h'' τ
        simp only [Pi.mul_apply, coe_ρHom_apply, inv_inv, Function.comp_apply] at this ⊢
        rw [this]
      · rw [map_ne_zero_iff _ (IsFractionRing.injective (ring N) K)]
        intro h0
        apply hb0
        have h1 := congrArg (fun F : ring N => (F : ℍ → ℂ)) h0
        simp only [ZeroMemClass.coe_zero] at h1
        funext τ
        have := congrFun h1 (γ⁻¹ • τ)
        simp only [coe_ρHom_apply, Pi.zero_apply, inv_inv, smul_inv_smul] at this
        exact this
    obtain ⟨p, q, hq, hpq⟩ := invariant_fraction N a b a.2 b.2 hb0 hinv

    have hqK : Polynomial.aeval (jK N K) q ≠ 0 := aeval_jK_ne_zero N K hq
    have hab : algebraMap (ring N) K a / algebraMap (ring N) K b =
        Polynomial.aeval (jK N K) p / Polynomial.aeval (jK N K) q := by
      rw [div_eq_div_iff hbK hqK]
      change algebraMap (ring N) K a * Polynomial.aeval (algebraMap (ring N) K (jGen N)) q =
        Polynomial.aeval (algebraMap (ring N) K (jGen N)) p * algebraMap (ring N) K b
      rw [Polynomial.aeval_algebraMap_apply, Polynomial.aeval_algebraMap_apply, ← map_mul,
        ← map_mul]
      congr 1
      apply Subtype.ext
      funext τ
      have := congrFun hpq τ
      simp only [Pi.mul_apply] at this
      simp only [Subalgebra.coe_mul, Pi.mul_apply, coe_aeval_jGen]
      rw [this, mul_comm]
    rw [hab]
    exact div_mem
      (IntermediateField.algebra_adjoin_le_adjoin ℂ _ (Polynomial.aeval_mem_adjoin_singleton ℂ _))
      (IntermediateField.algebra_adjoin_le_adjoin ℂ _ (Polynomial.aeval_mem_adjoin_singleton ℂ _))
  ·
    rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff, SetLike.mem_coe,
      IntermediateField.mem_fixedField_iff]
    rintro _ ⟨γ, rfl⟩
    exact σHom_jK N K γ
private theorem finite_range : Finite (σHom N K).range := by
  have h := Subgroup.index_ker (σHom N K)
  rw [ker_σHom_eq] at h
  exact Nat.finite_of_card_ne_zero (h ▸ Subgroup.FiniteIndex.index_ne_zero)
private theorem natCard_range : Nat.card (σHom N K).range = (Gpm N).index := by
  rw [← ker_σHom_eq N K, Subgroup.index_ker]
private theorem isGalois_fixedField : IsGalois (IntermediateField.fixedField (σHom N K).range) K := by
  have := finite_range N K
  exact IsGalois.of_fixed_field K (σHom N K).range
set_option linter.style.haveILetI false in
private theorem finrank_fixedField :
    Module.finrank (IntermediateField.fixedField (σHom N K).range) K = (Gpm N).index := by
  haveI := finite_range N K
  haveI := Fintype.ofFinite (σHom N K).range
  rw [← natCard_range N K, Nat.card_eq_fintype_card]
  exact FixedPoints.finrank_eq_card (σHom N K).range K
private theorem finiteDimensional_fixedField :
    FiniteDimensional (IntermediateField.fixedField (σHom N K).range) K := by
  apply Module.finite_of_finrank_pos
  rw [finrank_fixedField]
  exact Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
private theorem main :
    ∃ (hst : ∀ γ : SL(2, ℤ), ∀ F ∈ ModularCurve.LevelN.ring N,
        (fun τ : UpperHalfPlane => F (γ • τ)) ∈ ModularCurve.LevelN.ring N)
      (σ : SL(2, ℤ) →* (K ≃ₐ[ℂ] K)),
      (∀ (γ : SL(2, ℤ)) (F : UpperHalfPlane → ℂ) (hF : F ∈ ModularCurve.LevelN.ring N),
          σ γ (algebraMap (ModularCurve.LevelN.ring N) K ⟨F, hF⟩) =
            algebraMap (ModularCurve.LevelN.ring N) K
              ⟨fun τ : UpperHalfPlane => F (γ⁻¹ • τ), hst γ⁻¹ F hF⟩) ∧
      σ.ker = CongruenceSubgroup.Gamma N ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) ∧
      IntermediateField.fixedField σ.range =
        IntermediateField.adjoin ℂ
          ({algebraMap (ModularCurve.LevelN.ring N) K (ModularCurve.LevelN.jGen N)} : Set K) ∧
      Transcendental ℂ (algebraMap (ModularCurve.LevelN.ring N) K (ModularCurve.LevelN.jGen N)) ∧
      FiniteDimensional
          (IntermediateField.adjoin ℂ
            ({algebraMap (ModularCurve.LevelN.ring N) K (ModularCurve.LevelN.jGen N)} : Set K)) K ∧
      Module.finrank
          (IntermediateField.adjoin ℂ
            ({algebraMap (ModularCurve.LevelN.ring N) K (ModularCurve.LevelN.jGen N)} : Set K)) K =
        (CongruenceSubgroup.Gamma N ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index ∧
      IsGalois
          (IntermediateField.adjoin ℂ
            ({algebraMap (ModularCurve.LevelN.ring N) K (ModularCurve.LevelN.jGen N)} : Set K)) K := by
  refine ⟨fun γ F hF => comp_smul_mem N γ hF, σHom N K, fun γ F hF => σHom_algebraMap' N K γ F hF,
    ker_σHom_eq N K, fixedField_eq N K, transcendental_jK N K, ?_, ?_, ?_⟩
  · rw [← fixedField_eq N K]; exact finiteDimensional_fixedField N K
  · rw [← fixedField_eq N K]; exact finrank_fixedField N K
  · rw [← fixedField_eq N K]; exact isGalois_fixedField N K

end FractionField
end GaloisStructure

/-- Pin `ModularCurve.LevelN.exists_monoidHom_algEquiv_fixedField_eq_adjoin`
(`S_..._exists_monoidHom_algEquiv_fixedField_eq_adjoin.lean:446`), at the wrapper's
statement. -/
theorem exists_monoidHom_algEquiv_fixedField_eq_adjoin (N : ℕ) [NeZero N]
    (K : Type*) [Field K] [Algebra ℂ K] [Algebra (ModularCurve.LevelN.ring N) K]
    [IsScalarTower ℂ (ModularCurve.LevelN.ring N) K]
    [IsFractionRing (ModularCurve.LevelN.ring N) K] :
    ∃ (hst : ∀ γ : SL(2, ℤ), ∀ F ∈ ModularCurve.LevelN.ring N,
        (fun τ : UpperHalfPlane => F (γ • τ)) ∈ ModularCurve.LevelN.ring N)
      (σ : SL(2, ℤ) →* (K ≃ₐ[ℂ] K)),
      (∀ (γ : SL(2, ℤ)) (F : UpperHalfPlane → ℂ) (hF : F ∈ ModularCurve.LevelN.ring N),
          σ γ (algebraMap (ModularCurve.LevelN.ring N) K ⟨F, hF⟩) =
            algebraMap (ModularCurve.LevelN.ring N) K
              ⟨fun τ : UpperHalfPlane => F (γ⁻¹ • τ), hst γ⁻¹ F hF⟩) ∧
      σ.ker = CongruenceSubgroup.Gamma N ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) ∧
      IntermediateField.fixedField σ.range =
        IntermediateField.adjoin ℂ
          ({algebraMap (ModularCurve.LevelN.ring N) K (ModularCurve.LevelN.jGen N)} : Set K) ∧
      Transcendental ℂ (algebraMap (ModularCurve.LevelN.ring N) K (ModularCurve.LevelN.jGen N)) ∧
      FiniteDimensional
          (IntermediateField.adjoin ℂ
            ({algebraMap (ModularCurve.LevelN.ring N) K (ModularCurve.LevelN.jGen N)} : Set K)) K ∧
      Module.finrank
          (IntermediateField.adjoin ℂ
            ({algebraMap (ModularCurve.LevelN.ring N) K (ModularCurve.LevelN.jGen N)} : Set K)) K =
        (CongruenceSubgroup.Gamma N ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index ∧
      IsGalois
          (IntermediateField.adjoin ℂ
            ({algebraMap (ModularCurve.LevelN.ring N) K (ModularCurve.LevelN.jGen N)} : Set K)) K :=
  GaloisStructure.main N K

namespace QExpEmbedding

section Expansion

local notation "Δ" => ModularForm.discriminant

variable (N : ℕ) [NeZero N]



private theorem PB.add_right {F : ℍ → ℂ} {m : ℕ} (hm : PB F m) (k : ℕ) : PB F (m + k) := by
  unfold PB at hm ⊢
  rw [pow_add, ← mul_assoc]
  exact hm.mul ((good_discriminant 1).pow k).bdd

open Classical in

private def poleOrder (F : ring N) : ℕ := Nat.find (exists_isBoundedAtImInfty_mul_pow N F.2)
private theorem poleOrder_spec (F : ring N) : PB (F : ℍ → ℂ) (poleOrder N F) := by
  classical
  exact Nat.find_spec (exists_isBoundedAtImInfty_mul_pow N F.2)
private def qexpFun (F : ring N) : LaurentSeries ℂ :=
  Q N ((F : ℍ → ℂ) * (Δ : ℍ → ℂ) ^ poleOrder N F) / Q N (Δ : ℍ → ℂ) ^ poleOrder N F
private theorem qexpFun_mul_pow (F : ring N) {m : ℕ} (hm : PB (F : ℍ → ℂ) m) :
    qexpFun N F * Q N (Δ : ℍ → ℂ) ^ m = Q N ((F : ℍ → ℂ) * (Δ : ℍ → ℂ) ^ m) := by
  have hN := castN_pos N
  set m₀ := poleOrder N F with hm₀
  have hm₀' : PB (F : ℍ → ℂ) m₀ := poleOrder_spec N F
  have hΔ0 : Q N (Δ : ℍ → ℂ) ≠ 0 := Q_discriminant_ne_zero N
  have hgood₀ := good_of_PB N F.2 hm₀'
  have hgoodm := good_of_PB N F.2 hm

  have hkey : Q N ((F : ℍ → ℂ) * (Δ : ℍ → ℂ) ^ m₀) * Q N (Δ : ℍ → ℂ) ^ m =
      Q N ((F : ℍ → ℂ) * (Δ : ℍ → ℂ) ^ m) * Q N (Δ : ℍ → ℂ) ^ m₀ := by
    rw [← Q_pow hN (good_discriminant N), ← Q_pow hN (good_discriminant N),
      ← Q_mul hN hgood₀ ((good_discriminant N).pow m), ← Q_mul hN hgoodm ((good_discriminant N).pow m₀)]
    congr 1
    ring
  rw [qexpFun, div_mul_eq_mul_div, div_eq_iff (pow_ne_zero _ hΔ0), hkey]
private def qexpA : ring N →+* LaurentSeries ℂ where
  toFun := qexpFun N
  map_one' := by
    have h := qexpFun_mul_pow N 1 (m := 0) (by
      change IsBoundedAtImInfty (((1 : ring N) : ℍ → ℂ) * (Δ : ℍ → ℂ) ^ 0)
      rw [pow_zero, mul_one, OneMemClass.coe_one]
      exact (Good.one (N : ℝ)).bdd)
    rw [pow_zero, mul_one, pow_zero, mul_one, OneMemClass.coe_one] at h
    rw [h, Q_one]
  map_mul' F G := by
    have hΔ0 : Q N (Δ : ℍ → ℂ) ≠ 0 := Q_discriminant_ne_zero N
    have hN := castN_pos N
    obtain hF := poleOrder_spec N F
    obtain hG := poleOrder_spec N G
    set mF := poleOrder N F
    set mG := poleOrder N G
    have hFG : PB (((F * G : ring N)) : ℍ → ℂ) (mF + mG) := by
      change IsBoundedAtImInfty (((F : ℍ → ℂ) * (G : ℍ → ℂ)) * (Δ : ℍ → ℂ) ^ (mF + mG))
      have : ((F : ℍ → ℂ) * (G : ℍ → ℂ)) * (Δ : ℍ → ℂ) ^ (mF + mG) =
          ((F : ℍ → ℂ) * (Δ : ℍ → ℂ) ^ mF) * ((G : ℍ → ℂ) * (Δ : ℍ → ℂ) ^ mG) := by ring
      rw [this]; exact hF.mul hG
    have h := qexpFun_mul_pow N (F * G) hFG
    have h2 : (((F * G : ring N)) : ℍ → ℂ) * (Δ : ℍ → ℂ) ^ (mF + mG) =
        ((F : ℍ → ℂ) * (Δ : ℍ → ℂ) ^ mF) * ((G : ℍ → ℂ) * (Δ : ℍ → ℂ) ^ mG) := by
      change ((F : ℍ → ℂ) * (G : ℍ → ℂ)) * (Δ : ℍ → ℂ) ^ (mF + mG) = _; ring
    rw [h2, Q_mul hN (good_of_PB N F.2 hF) (good_of_PB N G.2 hG), ← qexpFun_mul_pow N F hF,
      ← qexpFun_mul_pow N G hG] at h
    apply mul_right_cancel₀ (pow_ne_zero (mF + mG) hΔ0)
    rw [h]; ring
  map_zero' := by
    have h := qexpFun_mul_pow N 0 (m := 0) (by
      change IsBoundedAtImInfty (((0 : ring N) : ℍ → ℂ) * (Δ : ℍ → ℂ) ^ 0)
      rw [ZeroMemClass.coe_zero, zero_mul]
      exact (Good.const (N : ℝ) 0).bdd)
    rw [pow_zero, mul_one, ZeroMemClass.coe_zero, zero_mul] at h
    rw [h]
    simp only [Q, qExpansion_zero, map_zero]
  map_add' F G := by
    have hΔ0 : Q N (Δ : ℍ → ℂ) ≠ 0 := Q_discriminant_ne_zero N
    have hN := castN_pos N
    have hF := (poleOrder_spec N F).add_right (poleOrder N G)
    have hG' := (poleOrder_spec N G).add_right (poleOrder N F)
    set m := poleOrder N F + poleOrder N G with hm
    have hG : PB (G : ℍ → ℂ) m := by rw [hm, add_comm]; exact hG'
    have hFG : PB (((F + G : ring N)) : ℍ → ℂ) m := by
      change IsBoundedAtImInfty (((F : ℍ → ℂ) + (G : ℍ → ℂ)) * (Δ : ℍ → ℂ) ^ m)
      rw [add_mul]; exact hF.add hG
    have h := qexpFun_mul_pow N (F + G) hFG
    have h2 : (((F + G : ring N)) : ℍ → ℂ) * (Δ : ℍ → ℂ) ^ m =
        (F : ℍ → ℂ) * (Δ : ℍ → ℂ) ^ m + (G : ℍ → ℂ) * (Δ : ℍ → ℂ) ^ m := by
      change ((F : ℍ → ℂ) + (G : ℍ → ℂ)) * (Δ : ℍ → ℂ) ^ m = _; ring
    rw [h2, Q_add hN (good_of_PB N F.2 hF) (good_of_PB N G.2 hG), ← qexpFun_mul_pow N F hF,
      ← qexpFun_mul_pow N G hG] at h
    apply mul_right_cancel₀ (pow_ne_zero m hΔ0)
    rw [h]; ring
private theorem qexpA_apply (F : ring N) : qexpA N F = qexpFun N F := rfl
private theorem qexpA_mul_pow (F : ℍ → ℂ) (hF : F ∈ ring N) {m : ℕ} (hm : IsBoundedAtImInfty (F * (Δ : ℍ → ℂ) ^ m)) :
    qexpA N ⟨F, hF⟩ * Q N (Δ : ℍ → ℂ) ^ m = Q N (F * (Δ : ℍ → ℂ) ^ m) :=
  qexpFun_mul_pow N ⟨F, hF⟩ hm
private theorem qexpA_algebraMap (c : ℂ) : qexpA N (algebraMap ℂ (ring N) c) = HahnSeries.C c := by
  have hcoe : ((algebraMap ℂ (ring N) c : ring N) : ℍ → ℂ) = fun _ => c := by
    funext τ; simp [Algebra.algebraMap_eq_smul_one]
  have h := qexpA_mul_pow N (fun _ : ℍ => c) (by rw [← hcoe]; exact (algebraMap ℂ (ring N) c).2)
    (m := 0) (by rw [pow_zero, mul_one]; exact (Good.const (N : ℝ) c).bdd)
  rw [pow_zero, mul_one, pow_zero, mul_one, Q_const (castN_pos N)] at h
  have hc : algebraMap ℂ (ring N) c = ⟨fun _ : ℍ => c, by rw [← hcoe]; exact (algebraMap ℂ (ring N) c).2⟩ :=
    Subtype.ext hcoe
  rw [hc]
  exact h
private theorem qexpA_injective : Function.Injective (qexpA N) := by
  intro F G hFG
  rw [← sub_eq_zero] at hFG ⊢
  rw [← map_sub] at hFG
  set H := F - G
  have hm := poleOrder_spec N H
  have h := qexpA_mul_pow N (H : ℍ → ℂ) H.2 hm
  rw [show (⟨(H : ℍ → ℂ), H.2⟩ : ring N) = H from rfl, hFG, zero_mul, eq_comm,
    Q_eq_zero_iff (castN_pos N) (good_of_PB N H.2 hm), mul_discriminant_pow_eq_zero_iff] at h
  exact Subtype.ext h

variable (K : Type*) [Field K] [Algebra ℂ K] [Algebra (ring N) K] [IsScalarTower ℂ (ring N) K]
  [IsFractionRing (ring N) K]
private theorem algebraMap_laurentSeries (c : ℂ) : algebraMap ℂ (LaurentSeries ℂ) c = HahnSeries.C c := by
  have h1 : algebraMap ℂ (PowerSeries ℂ) c = PowerSeries.C c := by simp
  rw [HahnSeries.algebraMap_apply', h1, HahnSeries.ofPowerSeries_C]
private def qexpK : K →ₐ[ℂ] LaurentSeries ℂ :=
  { IsFractionRing.lift (qexpA_injective N) with
    commutes' := fun c => by
      change IsFractionRing.lift (qexpA_injective N) (algebraMap ℂ K c) = _
      rw [IsScalarTower.algebraMap_apply ℂ (ring N) K, IsFractionRing.lift_algebraMap,
        qexpA_algebraMap, algebraMap_laurentSeries] }
private theorem qexpK_algebraMap (F : ring N) : qexpK N K (algebraMap (ring N) K F) = qexpA N F := by
  change IsFractionRing.lift (qexpA_injective N) (algebraMap (ring N) K F) = _
  exact IsFractionRing.lift_algebraMap (qexpA_injective N) F

end Expansion
end QExpEmbedding

namespace QExpEmbedding

section Width

local notation "Δ" => ModularForm.discriminant

variable (N : ℕ) [NeZero N]




private theorem jAnalytic_mul_discriminant :
    jAnalytic * (Δ : ℍ → ℂ) ^ 1 = (ModularForm.E₄ : ℍ → ℂ) ^ 3 := by
  funext τ
  simp only [Pi.mul_apply, Pi.pow_apply, pow_one, jAnalytic]
  field_simp [ModularForm.discriminant_ne_zero τ]
private theorem isBoundedAtImInfty_jAnalytic_mul :
    IsBoundedAtImInfty (jAnalytic * (Δ : ℍ → ℂ) ^ 1) := by
  rw [jAnalytic_mul_discriminant]
  exact ((good_E₄ 1).pow 3).bdd

variable (K : Type*) [Field K] [Algebra ℂ K] [Algebra (ring N) K] [IsScalarTower ℂ (ring N) K]
  [IsFractionRing (ring N) K]
private theorem qexpK_jGen : qexpK N K (algebraMap (ring N) K (jGen N)) = ModularCurve.qExpand ℂ N (ModularCurve.jqModC ℂ) := by
  have hN := castN_pos N
  have hΔ0 : Q N (Δ : ℍ → ℂ) ≠ 0 := Q_discriminant_ne_zero N
  rw [qexpK_algebraMap]
  have h := qexpA_mul_pow N jAnalytic (jAnalytic_mem N) isBoundedAtImInfty_jAnalytic_mul
  rw [pow_one, jAnalytic_mul_discriminant, Q_pow hN (good_E₄ N) 3] at h
  change qexpA N (jGen N) * Q N (Δ : ℍ → ℂ) = Q N (ModularForm.E₄ : ℍ → ℂ) ^ 3 at h
  rw [← eq_div_iff hΔ0] at h
  have hE : Good 1 (ModularForm.E₄ : ℍ → ℂ) := by simpa using good_E₄ 1
  have hD : Good 1 (Δ : ℍ → ℂ) := by simpa using good_discriminant 1
  rw [h, Q_natCast_eq_qExpand N hE, Q_natCast_eq_qExpand N hD, ← map_pow, ← map_div₀,
    ModularCurve.jqModC_eq_qExpansion_E4_cube_div_discriminant]
  rfl

end Width
end QExpEmbedding

/-- Pin `ModularCurve.LevelN.exists_algHom_laurentSeries_qExpansion`
(`S_..._exists_algHom_laurentSeries_qExpansion.lean:586`), at the wrapper's statement. -/
theorem exists_algHom_laurentSeries_qExpansion (N : ℕ) [NeZero N]
    (K : Type*) [Field K] [Algebra ℂ K] [Algebra (ModularCurve.LevelN.ring N) K]
    [IsScalarTower ℂ (ModularCurve.LevelN.ring N) K]
    [IsFractionRing (ModularCurve.LevelN.ring N) K] :
    ∃ E : K →ₐ[ℂ] LaurentSeries ℂ,
      E (algebraMap (ModularCurve.LevelN.ring N) K (ModularCurve.LevelN.jGen N)) =
          ModularCurve.qExpand ℂ N (ModularCurve.jqModC ℂ) ∧
      ∀ (F : UpperHalfPlane → ℂ) (hF : F ∈ ModularCurve.LevelN.ring N) (m : ℕ),
        UpperHalfPlane.IsBoundedAtImInfty (F * ModularForm.discriminant ^ m) →
        E (algebraMap (ModularCurve.LevelN.ring N) K ⟨F, hF⟩) *
            HahnSeries.ofPowerSeries ℤ ℂ
              (UpperHalfPlane.qExpansion N (ModularForm.discriminant : UpperHalfPlane → ℂ)) ^ m =
          HahnSeries.ofPowerSeries ℤ ℂ
            (UpperHalfPlane.qExpansion N (F * ModularForm.discriminant ^ m)) := by
  refine ⟨QExpEmbedding.qexpK N K, QExpEmbedding.qexpK_jGen N K, fun F hF m hm => ?_⟩
  rw [QExpEmbedding.qexpK_algebraMap]
  exact QExpEmbedding.qexpA_mul_pow N F hF hm


end LevelN

end ModularCurve

end
