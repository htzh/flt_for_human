/-
  The three `CuspForm.Stable*` theorems: the hypotheses of the Hecke-equivariance
  layer, discharged.

  `StableD`, `StableU`, `StableT`
  (`ModularForms/Defs/GammaH.lean`, transcribed from the tail of
  `Definitions/Def_CuspForm_HeckeOperatorFormsGammaH.lean`) are the statements
  that the diamond action, `U_q`, and the `T_ℓ` combination
  `U_ℓ f + f ∣ (ρ · diag ℓ)` again land in `Γ_H(M)`-cusp forms. This module proves
  all three. Each is a three-component conjunction (invariance, holomorphic,
  cuspidal), and each component is one already-ported lemma:

  | component | lemma |
  |---|---|
  | `Γ_H`-invariance of `U_q` | `ModularForm.heckeU_slash_eq_self_of_mem_GammaH` (W3b, node 8) |
  | `Γ_H`-invariance of `U_ℓ + f ∣ (ρ · diag ℓ)` | `ModularForm.heckeU_add_slash_slash_eq_self_of_mem_GammaH` (W3b, node 9) |
  | holomorphy | `ModularForm.mdifferentiable_heckeU` |
  | vanishing at cusps under `U_p` | `CuspFormClass.isZeroAt_heckeU` |
  | vanishing at cusps under `∣[k] σ` | `CuspFormClass.isZeroAt_slash_of_mem_Gamma0` |
  | vanishing at cusps under `∣[k] σ ∣[k] diag ℓ` | `CuspFormClass.isZeroAt_slash_slash_heckeDiagMatrix_of_mem_Gamma0` |

  Keeping these out of `ModularForms/HeckeInvariance.lean` leaves that module's
  "statements about `U_p`/`T_p` themselves" scope intact.

  ## The period lattice is stable under the three Hecke-diamond operators (MC-4a)

  The second half of the module (§"Final") is the row
  `ModularCurve.periodLatticeOf_gammaH_heckeDiamondStable`: with the three
  `Stable*` hypotheses now discharged, the `ℤ`-lattice
  `periodLatticeOf (GammaH M H)` is stable under the `dualMap` of
  `heckeTLinH 2 hℓ hℓM` (`ℓ` prime, `ℓ ∤ M`), of `heckeULinH 2 q` (`q ∣ M`),
  and of `diamondLinH 2 d`. Its proof is the pin's 464-line `S_` file, ported in
  full:

  * `PeriodLatticeHStableProof` is the pin's engine namespace — `IsPrimitive`
    with its `add`/`sum`/`exists_const` lemmas, the ball-cover construction
    `exists_isPrimitive`, the derivative/period dictionary
    (`integral_segment_eq`, `slash_two`, `Φ`, `Φ_smul_sub_Φ`, `mkQ_Φ_smul`), and
    the coset engine `dualMap_period_eq`/`sum_mkQ_Φ_smul_eq`/`dualMap_period_mem`
    plus the three operator instances. **The whole engine is `private` here**:
    the wire (`Thm_…` + its `S_` copy) has a statement for the headline only, and
    `IsPrimitive` in particular is local scaffolding that must not grow as port
    surface. `private` also keeps the statement checker diffing the headline
    alone.
  * `span_stable` (the pin's own `private` helper) inducts on `Submodule.span`
    membership, and the three `periodLatticeOf_stable_*` assemblies are the
    pin's `Final` section.

  Nothing else is public: the module's only new name is the headline. The pin's
  `p2m_export`/`p2m_open` lines are P2M scaffolding, not Lean, and are not
  transcribed.

  FLT provenance, pinned `aa2d8b3`:

  spec-pin: Theorems/Thm_ModularCurve_periodLatticeOf_gammaH_heckeDiamondStable.lean
  spec-pin: P2M/Sol/S_ModularCurve_periodLatticeOf_gammaH_heckeDiamondStable.lean   -- comparable copy
  spec-pin: Theorems/Thm_CuspForm_stableD.lean
  spec-pin: P2M/Sol/S_CuspForm_stableD.lean   -- comparable copy
  spec-pin: Theorems/Thm_CuspForm_stableU.lean
  spec-pin: P2M/Sol/S_CuspForm_stableU.lean   -- comparable copy
  spec-pin: Theorems/Thm_CuspForm_stableT.lean
  spec-pin: P2M/Sol/S_CuspForm_stableT.lean   -- comparable copy
-/
import FLTForHuman.ModularForms.Defs.GammaH
import FLTForHuman.ModularForms.HeckeInvariance
import FLTForHuman.ModularForms.CuspFormSlashHecke
import FLTForHuman.ModularForms.HeckeAnalytic
import FLTForHuman.ModularForms.HeckeCusps
import FLTForHuman.ModularForms.EichlerShimura.PeriodOf

set_option autoImplicit false

-- The pin's `haveI : NeZero ℓ` before the conclusion is part of its proof text
-- (`stableT`); kept literal, as in `HeckeInvariance.lean` and `Corestriction.lean`.
set_option linter.style.haveILetI false

noncomputable section

open UpperHalfPlane CongruenceSubgroup

open scoped MatrixGroups ModularForm

open CohCarrier

namespace CuspForm

/-- Slashing by a `Γ₀(M)`-matrix preserves cuspidality for `Γ_H(M)`-cusp forms. -/
theorem stableD (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ) :
    CuspForm.StableD M H k := by
  intro σ f c hc
  exact CuspFormClass.isZeroAt_slash_of_mem_Gamma0 M H k σ f hc

/-- `U_q f` is again `Γ_H(M)`-invariant, holomorphic and cuspidal, for `q ∣ M`. -/
theorem stableU (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ) {q : ℕ}
    (hq : q.Prime) (hqM : q ∣ M) :
    CuspForm.StableU M H k q := by
  intro f
  exact ⟨fun γ hγ => ModularForm.heckeU_slash_eq_self_of_mem_GammaH M H k hq hqM
      (fun γ hγ => SlashInvariantFormClass.slash_action_eq f γ hγ) γ hγ,
    ModularForm.mdifferentiable_heckeU (CuspFormClass.holo f) k q,
    fun c hc => CuspFormClass.isZeroAt_heckeU f q hc⟩

/-- The `T_ℓ` combination `U_ℓ f + f ∣ (ρ · diag ℓ)` is again
`Γ_H(M)`-invariant, holomorphic and cuspidal, for `ℓ` prime and `ℓ ∤ M`. -/
theorem stableT (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ) {ℓ : ℕ}
    (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) :
    CuspForm.StableT M H k ℓ := by
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  intro ρ hρ f
  refine ⟨fun γ hγ => ModularForm.heckeU_add_slash_slash_eq_self_of_mem_GammaH M H k hℓ hℓM ρ hρ
      (fun γ hγ => SlashInvariantFormClass.slash_action_eq f γ hγ) γ hγ,
    (ModularForm.mdifferentiable_heckeU (CuspFormClass.holo f) k ℓ).add
      ((CuspFormClass.holo f).slash k _),
    fun c hc => ?_⟩
  rw [SlashAction.slash_mul]
  exact (CuspFormClass.isZeroAt_heckeU f ℓ hc).add
    (CuspFormClass.isZeroAt_slash_slash_heckeDiagMatrix_of_mem_Gamma0 M H k ℓ ρ f hc)

end CuspForm

namespace ModularCurve

open Filter Topology

open scoped Manifold

namespace PeriodLatticeHStableProof

/-! ### Primitives: the pin's `IsPrimitive` scaffolding

`PeriodLatticeHStableProof` is the pin's engine namespace
(`P2M/Sol/S_ModularCurve_periodLatticeOf_gammaH_heckeDiamondStable.lean:23–412`),
transcribed here with every declaration `private` (see the module header). -/

/-- The pin's scaffolding: `G` is a primitive of `h` on `ℍ`. -/
private def IsPrimitive (h : ℍ → ℂ) (G : ℂ → ℂ) : Prop :=
  ∀ τ : ℍ, HasDerivAt G (h τ) (τ : ℂ)

private theorem IsPrimitive.add {h₁ h₂ : ℍ → ℂ} {G₁ G₂ : ℂ → ℂ} (h1 : IsPrimitive h₁ G₁)
    (h2 : IsPrimitive h₂ G₂) : IsPrimitive (h₁ + h₂) (G₁ + G₂) :=
  fun τ => (h1 τ).add (h2 τ)

private theorem IsPrimitive.sum {ι : Type*} (s : Finset ι) {h : ι → ℍ → ℂ} {G : ι → ℂ → ℂ}
    (hG : ∀ i ∈ s, IsPrimitive (h i) (G i)) :
    IsPrimitive (∑ i ∈ s, h i) (fun z => ∑ i ∈ s, G i z) := by
  intro τ
  have h' : (fun z => ∑ i ∈ s, G i z) = ∑ i ∈ s, G i := by
    ext z; simp [Finset.sum_apply]
  have := HasDerivAt.sum (u := s) (A := G) (A' := fun i => h i τ) (x := (τ : ℂ))
    (fun i hi => hG i hi τ)
  rw [h']
  simpa [Finset.sum_apply] using this

private theorem IsPrimitive.exists_const {h : ℍ → ℂ} {G G' : ℂ → ℂ} (hG : IsPrimitive h G)
    (hG' : IsPrimitive h G') : ∃ a : ℂ, ∀ τ : ℍ, G τ = G' τ + a := by
  obtain ⟨a, ha⟩ := isOpen_upperHalfPlaneSet.exists_eq_add_of_deriv_eq
    (convex_halfSpace_im_gt 0).isPreconnected
    (fun z hz => (hG ⟨z, hz⟩).differentiableAt.differentiableWithinAt)
    (fun z hz => (hG' ⟨z, hz⟩).differentiableAt.differentiableWithinAt)
    (fun z hz => by rw [(hG ⟨z, hz⟩).deriv, (hG' ⟨z, hz⟩).deriv])
  exact ⟨a, fun τ => ha τ.im_pos⟩

private theorem exists_isPrimitive {h : ℍ → ℂ} (hh : MDiff h) : ∃ G : ℂ → ℂ, IsPrimitive h G := by
  have hF : DifferentiableOn ℂ (h ∘ ofComplex) {z : ℂ | 0 < z.im} :=
    UpperHalfPlane.mdifferentiable_iff.mp hh

  let r : ℕ → ℝ := fun n => (n : ℝ) + 1
  let c : ℕ → ℂ := fun n => (r n : ℂ) * Complex.I
  have hr : ∀ n, 0 < r n := fun n => by positivity
  have hc_im : ∀ n, (c n).im = r n := fun n => by simp [c]
  have hc_re : ∀ n, (c n).re = 0 := fun n => by simp [c]
  have hsub : ∀ n, Metric.ball (c n) (r n) ⊆ {z : ℂ | 0 < z.im} := by
    intro n z hz
    rw [Metric.mem_ball, Complex.dist_eq] at hz
    have h1 : |(z - c n).im| ≤ ‖z - c n‖ := Complex.abs_im_le_norm _
    rw [Complex.sub_im, hc_im] at h1
    have h2 := (abs_lt.mp (lt_of_le_of_lt h1 hz)).1
    show 0 < z.im
    linarith
  have hI : ∀ n, Complex.I ∈ Metric.ball (c n) (r n) := by
    intro n
    rw [Metric.mem_ball, Complex.dist_eq]
    have : Complex.I - c n = ((1 - r n : ℝ) : ℂ) * Complex.I := by
      simp only [c]; push_cast; ring
    rw [this, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs]
    simp only [r]
    rw [abs_lt]; constructor <;> linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hcover : ∀ z : ℂ, 0 < z.im → ∃ n : ℕ, z ∈ Metric.ball (c n) (r n) := by
    intro z hz
    obtain ⟨n, hn⟩ := exists_nat_gt (‖z‖ ^ 2 / (2 * z.im))
    refine ⟨n, ?_⟩
    rw [Metric.mem_ball, Complex.dist_eq]
    have hn' : ‖z‖ ^ 2 / (2 * z.im) < r n := lt_of_lt_of_le hn (by simp [r])
    have h2 : ‖z‖ ^ 2 < 2 * z.im * r n := by
      rwa [div_lt_iff₀ (by positivity), mul_comm] at hn'
    have hsq : ‖z - c n‖ ^ 2 = ‖z‖ ^ 2 - 2 * z.im * r n + r n ^ 2 := by
      rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply,
        Complex.sub_re, Complex.sub_im, hc_re, hc_im]
      ring
    have h3 : ‖z - c n‖ ^ 2 < r n ^ 2 := by rw [hsq]; linarith
    exact lt_of_pow_lt_pow_left₀ 2 (hr n).le h3
  have hmono : ∀ {n m : ℕ}, n ≤ m → Metric.ball (c n) (r n) ⊆ Metric.ball (c m) (r m) := by
    intro n m hnm z hz
    rw [Metric.mem_ball] at hz ⊢
    have hd : dist (c n) (c m) = r m - r n := by
      rw [Complex.dist_eq]
      have : c n - c m = ((r n - r m : ℝ) : ℂ) * Complex.I := by
        simp only [c]; push_cast; ring
      rw [this, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs,
        abs_sub_comm, abs_of_nonneg]
      simp only [r]; linarith [(Nat.cast_le.mpr hnm : (n : ℝ) ≤ m)]
    calc dist z (c m) ≤ dist z (c n) + dist (c n) (c m) := dist_triangle _ _ _
      _ < r n + (r m - r n) := by rw [hd]; linarith
      _ = r m := by ring

  have hex : ∀ n, ∃ g : ℂ → ℂ, g Complex.I = 0 ∧
      ∀ z ∈ Metric.ball (c n) (r n), HasDerivAt g ((h ∘ ofComplex) z) z :=
    fun n => ((hF.mono (hsub n)).isExactOn_ball).with_val_at Complex.I 0
  choose g hg0 hg using hex
  have hagree : ∀ {n m : ℕ}, n ≤ m → Set.EqOn (g n) (g m) (Metric.ball (c n) (r n)) := by
    intro n m hnm
    refine Metric.isOpen_ball.eqOn_of_deriv_eq (convex_ball _ _).isPreconnected ?_ ?_ ?_ (hI n) ?_
    · exact fun z hz => (hg n z hz).differentiableAt.differentiableWithinAt
    · exact fun z hz => (hg m z (hmono hnm hz)).differentiableAt.differentiableWithinAt
    · exact fun z hz => by rw [(hg n z hz).deriv, (hg m z (hmono hnm hz)).deriv]
    · rw [hg0, hg0]
  classical
  let idx : ℂ → ℕ := fun z => if hz : 0 < z.im then Nat.find (hcover z hz) else 0
  have hidx : ∀ z : ℂ, (hz : 0 < z.im) → z ∈ Metric.ball (c (idx z)) (r (idx z)) := by
    intro z hz
    simp only [idx, dite_eq_left hz]
    exact Nat.find_spec (hcover z hz)
  refine ⟨fun z => g (idx z) z, fun τ => ?_⟩
  have hτ := hidx τ τ.im_pos
  have key : (fun z => g (idx z) z) =ᶠ[𝓝 (τ : ℂ)] g (idx τ) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hτ] with w hw
    have hw' : 0 < w.im := hsub _ hw
    rcases le_total (idx w) (idx (τ : ℂ)) with hle | hle
    · exact hagree hle (hidx w hw')
    · exact (hagree hle hw).symm
  have := (hg (idx (τ : ℂ)) τ hτ).congr_of_eventuallyEq key
  simpa [Function.comp, ofComplex_apply] using this

private theorem IsPrimitive.integral_segment_eq {h : ℍ → ℂ} {G : ℂ → ℂ} (hG : IsPrimitive h G)
    (hc : Continuous h) (τ₀ τ₁ : ℍ) :
    ∫ t in (0 : ℝ)..1, h (segmentPath τ₀ τ₁ t) * ((τ₁ : ℂ) - τ₀) = G τ₁ - G τ₀ := by
  have h0 : segmentPoint τ₀ τ₁ 0 = τ₀ := by simp [segmentPoint, clamp01]
  have h1 : segmentPoint τ₀ τ₁ 1 = τ₁ := by simp [segmentPoint, clamp01]
  have hcontG : Continuous fun t => G (segmentPoint τ₀ τ₁ t) :=
    continuous_iff_continuousAt.mpr fun t =>
      ContinuousAt.comp (g := G) (f := segmentPoint τ₀ τ₁) (x := t)
        (hG (segmentPath τ₀ τ₁ t)).continuousAt (continuous_segmentPoint τ₀ τ₁).continuousAt
  have hderiv : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt (fun t => G (segmentPoint τ₀ τ₁ t)) (h (segmentPath τ₀ τ₁ t) * ((τ₁ : ℂ) - τ₀)) t := by
    intro t ht
    have hlin : HasDerivAt (fun s : ℝ => (1 - (s : ℂ)) * (τ₀ : ℂ) + (s : ℂ) * τ₁)
        ((τ₁ : ℂ) - τ₀) t :=
      hasDerivAt_affine (τ₀ : ℂ) (τ₁ : ℂ) t
    have heq : segmentPoint τ₀ τ₁ =ᶠ[𝓝 t] fun s : ℝ => (1 - (s : ℂ)) * (τ₀ : ℂ) + (s : ℂ) * τ₁ := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
      rw [segmentPoint, clamp01_of_mem (Set.Ioo_subset_Icc_self hs), Complex.real_smul,
        Complex.real_smul]
      push_cast
      ring
    have hseg : HasDerivAt (segmentPoint τ₀ τ₁) ((τ₁ : ℂ) - τ₀) t :=
      hlin.congr_of_eventuallyEq heq
    exact (hG (segmentPath τ₀ τ₁ t)).comp t hseg
  have hint : IntervalIntegrable (fun t => h (segmentPath τ₀ τ₁ t) * ((τ₁ : ℂ) - τ₀))
      MeasureTheory.volume 0 1 :=
    ((hc.comp (continuous_segmentPath τ₀ τ₁)).mul continuous_const).intervalIntegrable 0 1
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hcontG.continuousOn hderiv
    hint, h0, h1]

private theorem IsPrimitive.slash_two {f : ℍ → ℂ} {G : ℂ → ℂ} (hG : IsPrimitive f G)
    {α : GL (Fin 2) ℝ} (hα : 0 < (α.det : ℝ)) :
    IsPrimitive (f ∣[(2 : ℤ)] α) (fun z => G (↑(α • ofComplex z))) := by
  have hα' : 0 < α.val.det := by rwa [Matrix.GeneralLinearGroup.val_det_apply] at hα
  intro τ
  have h1 : HasDerivAt (fun z : ℂ => ((α • ofComplex z : ℍ) : ℂ)) (↑(α.val.det) / denom α τ ^ 2) τ :=
    (hasStrictDerivAt_smul hα' τ).hasDerivAt
  have h2 : HasDerivAt G (f (α • τ)) ((fun z : ℂ => ((α • ofComplex z : ℍ) : ℂ)) τ) := by
    simp only [ofComplex_apply]
    exact hG (α • τ)
  have h3 := h2.comp (τ : ℂ) h1
  convert h3 using 1 <;> try rfl
  have hσ : σ α = ContinuousAlgEquiv.refl ℝ ℂ := by simp [σ, hα']
  rw [ModularForm.slash_apply, hσ, abs_of_pos hα, ← Matrix.GeneralLinearGroup.val_det_apply]
  simp only [ContinuousAlgEquiv.refl_apply]
  rw [show (2 : ℤ) - 1 = 1 by norm_num, zpow_one, zpow_neg, zpow_ofNat]
  have hd : denom α τ ≠ 0 := denom_ne_zero α τ
  field_simp

private theorem slash_zero_apply_of_det_eq_one (g : ℍ → ℂ) {γ : GL (Fin 2) ℝ} (hγ : γ.det = 1) (τ : ℍ) :
    (g ∣[(0 : ℤ)] γ) τ = g (γ • τ) := by
  have hσ : σ γ = ContinuousAlgEquiv.refl ℝ ℂ := by simp [σ, hγ]
  rw [ModularForm.slash_apply, hσ, hγ]
  simp

private theorem slash_zero_apply_of_det_pos (g : ℍ → ℂ) {α : GL (Fin 2) ℝ} (hα : 0 < (α.det : ℝ))
    (τ : ℍ) : (g ∣[(0 : ℤ)] α) τ = ((α.det : ℝ) : ℂ)⁻¹ * g (α • τ) := by
  have hα' : 0 < α.val.det := by rwa [Matrix.GeneralLinearGroup.val_det_apply] at hα
  have hσ : σ α = ContinuousAlgEquiv.refl ℝ ℂ := by simp [σ, hα']
  rw [ModularForm.slash_apply, hσ, abs_of_pos hα]
  simp [mul_comm]

private abbrev GammaHGL (M : ℕ) (H : Subgroup (ZMod M)ˣ) : Subgroup (GL (Fin 2) ℝ) :=
  ((CohCarrier.GammaH M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ)

private def Φ (τ : ℍ) : Module.Dual ℂ (CuspForm (CohCarrier.GammaH M H) 2) :=
  periodAlongOf (CohCarrier.GammaH M H) UpperHalfPlane.I τ

variable {M H}

private theorem Φ_apply_of_isPrimitive (τ : ℍ) (f : CuspForm (CohCarrier.GammaH M H) 2)
    {G : ℂ → ℂ} (hG : IsPrimitive ⇑f G) : Φ M H τ f = G τ - G UpperHalfPlane.I := by
  show periodAlongOf (CohCarrier.GammaH M H) UpperHalfPlane.I τ f = _
  rw [periodAlongOf_apply]
  exact hG.integral_segment_eq (CuspFormClass.holo f).continuous _ _

private theorem period_eq_Φ (g : CohCarrier.GammaH M H) :
    periodOf (CohCarrier.GammaH M H) g = Φ M H ((g : SL(2, ℤ)) • UpperHalfPlane.I) := rfl

private theorem Φ_smul_sub_Φ (g : CohCarrier.GammaH M H) (τ : ℍ) :
    Φ M H ((g : SL(2, ℤ)) • τ) - Φ M H τ = periodOf (CohCarrier.GammaH M H) g := by
  apply LinearMap.ext
  intro f
  obtain ⟨G, hG⟩ := exists_isPrimitive (CuspFormClass.holo f)
  have hmem : ((g : SL(2, ℤ)) : GL (Fin 2) ℝ) ∈ GammaHGL M H :=
    Subgroup.mem_map_of_mem (Matrix.SpecialLinearGroup.mapGL ℝ) g.2
  have hinv : (⇑f) ∣[(2 : ℤ)] ((g : SL(2, ℤ)) : GL (Fin 2) ℝ) = ⇑f :=
    SlashInvariantForm.slash_action_eqn f _ hmem
  have hdet : 0 < ((Matrix.GeneralLinearGroup.det ((g : SL(2, ℤ)) : GL (Fin 2) ℝ) : ℝ)) := by
    simp
  have hG' : IsPrimitive ⇑f (fun z => G ↑(((g : SL(2, ℤ)) : GL (Fin 2) ℝ) • ofComplex z)) := by
    have := hG.slash_two hdet
    rwa [hinv] at this
  obtain ⟨a, ha⟩ := hG'.exists_const hG
  have ha' : ∀ τ : ℍ, G ↑((g : SL(2, ℤ)) • τ) = G τ + a := fun τ => by
    simpa [ofComplex_apply] using ha τ
  rw [LinearMap.sub_apply, period_eq_Φ, Φ_apply_of_isPrimitive _ f hG,
    Φ_apply_of_isPrimitive _ f hG, Φ_apply_of_isPrimitive _ f hG, ha', ha']
  ring

private theorem Φ_smul_sub_Φ_mem {γ : GL (Fin 2) ℝ} (hγ : γ ∈ GammaHGL M H) (τ : ℍ) :
    Φ M H (γ • τ) - Φ M H τ ∈ periodLatticeOf (CohCarrier.GammaH M H) := by
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hγ
  have := Φ_smul_sub_Φ (M := M) (H := H) ⟨g, hg⟩ τ
  rw [ModularGroup.sl_moeb] at this
  rw [show Matrix.SpecialLinearGroup.mapGL ℝ g • τ = ((g : SL(2, ℤ)) : GL (Fin 2) ℝ) • τ from rfl,
    this]
  exact periodOf_mem_periodLatticeOf (CohCarrier.GammaH M H) _

private theorem mkQ_Φ_smul {γ : GL (Fin 2) ℝ} (hγ : γ ∈ GammaHGL M H) (τ : ℍ) :
    (periodLatticeOf (CohCarrier.GammaH M H)).mkQ (Φ M H (γ • τ)) = (periodLatticeOf (CohCarrier.GammaH M H)).mkQ (Φ M H τ) := by
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
  exact Φ_smul_sub_Φ_mem hγ τ

section Engine

variable {ι : Type*} [Fintype ι] (A : ι → GL (Fin 2) ℝ)

private theorem dualMap_period_eq (hA : ∀ i, 0 < ((A i).det : ℝ))
    (T : CuspForm (CohCarrier.GammaH M H) 2 →ₗ[ℂ] CuspForm (CohCarrier.GammaH M H) 2)
    (hT : ∀ f : CuspForm (CohCarrier.GammaH M H) 2, ⇑(T f) = ∑ i, (⇑f) ∣[(2 : ℤ)] A i)
    (g : CohCarrier.GammaH M H) :
    T.dualMap (periodOf (CohCarrier.GammaH M H) g) =
      ∑ i, (Φ M H (A i • (g : SL(2, ℤ)) • UpperHalfPlane.I) - Φ M H (A i • UpperHalfPlane.I)) := by
  apply LinearMap.ext
  intro f
  obtain ⟨G, hG⟩ := exists_isPrimitive (CuspFormClass.holo f)

  have hprim : IsPrimitive ⇑(T f) (fun z => ∑ i, G ↑(A i • ofComplex z)) := by
    rw [hT]
    exact IsPrimitive.sum Finset.univ (fun i _ => hG.slash_two (hA i))
  rw [LinearMap.dualMap_apply, period_eq_Φ, Φ_apply_of_isPrimitive _ _ hprim,
    LinearMap.sum_apply]
  simp only [LinearMap.sub_apply, Φ_apply_of_isPrimitive _ f hG, ofComplex_apply,
    Finset.sum_sub_distrib]
  ring

private theorem sum_mkQ_Φ_smul_eq {d : ℝ} (hd : 0 < d) (hA : ∀ i, ((A i).det : ℝ) = d)
    (hstab : ∀ g : ℍ → ℂ, (∀ γ ∈ GammaHGL M H, g ∣[(0 : ℤ)] γ = g) →
      ∀ γ ∈ GammaHGL M H, (∑ i, g ∣[(0 : ℤ)] A i) ∣[(0 : ℤ)] γ = ∑ i, g ∣[(0 : ℤ)] A i)
    {γ : GL (Fin 2) ℝ} (hγ : γ ∈ GammaHGL M H) (τ : ℍ) :
    ∑ i, (periodLatticeOf (CohCarrier.GammaH M H)).mkQ (Φ M H (A i • γ • τ)) = ∑ i, (periodLatticeOf (CohCarrier.GammaH M H)).mkQ (Φ M H (A i • τ)) := by
  classical
  set Φb : ℍ → (Module.Dual ℂ (CuspForm (CohCarrier.GammaH M H) 2)) ⧸ periodLatticeOf (CohCarrier.GammaH M H) :=
    fun τ => (periodLatticeOf (CohCarrier.GammaH M H)).mkQ (Φ M H τ) with hΦb
  have hΦb_inv : ∀ γ ∈ GammaHGL M H, ∀ τ : ℍ, Φb (γ • τ) = Φb τ := fun γ hγ τ => mkQ_Φ_smul hγ τ
  have hAdet : ∀ i, 0 < ((A i).det : ℝ) := fun i => (hA i).symm ▸ hd

  have hcount : ∀ v, (Finset.univ.filter fun i => v = Φb (A i • γ • τ)).card =
      (Finset.univ.filter fun i => v = Φb (A i • τ)).card := by
    intro v
    let g : ℍ → ℂ := fun τ => if v = Φb τ then 1 else 0
    have hg : ∀ γ ∈ GammaHGL M H, g ∣[(0 : ℤ)] γ = g := by
      intro γ hγ
      funext τ
      rw [slash_zero_apply_of_det_eq_one g (Subgroup.HasDetOne.det_eq hγ)]
      simp only [g, hΦb_inv γ hγ]
    have key := congr_fun (hstab g hg γ hγ) τ
    rw [slash_zero_apply_of_det_eq_one _ (Subgroup.HasDetOne.det_eq hγ)] at key
    simp only [Finset.sum_apply, slash_zero_apply_of_det_pos _ (hAdet _), hA,
      ← Finset.mul_sum] at key
    have hd' : ((d : ℝ) : ℂ)⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast hd.ne')
    have key' := mul_left_cancel₀ hd' key
    simp only [g, Finset.sum_boole] at key'
    exact_mod_cast key'
  have hms : (Finset.univ.val.map fun i => Φb (A i • γ • τ)) =
      Finset.univ.val.map fun i => Φb (A i • τ) := by
    refine Multiset.ext.mpr fun v => ?_
    rw [Multiset.count_map, Multiset.count_map]
    have := hcount v
    simpa [Finset.card_def, Finset.filter_val] using this
  show ∑ i, Φb (A i • γ • τ) = ∑ i, Φb (A i • τ)
  rw [Finset.sum_eq_multiset_sum, Finset.sum_eq_multiset_sum, hms]

private theorem dualMap_period_mem {d : ℝ} (hd : 0 < d) (hA : ∀ i, ((A i).det : ℝ) = d)
    (T : CuspForm (CohCarrier.GammaH M H) 2 →ₗ[ℂ] CuspForm (CohCarrier.GammaH M H) 2)
    (hT : ∀ f : CuspForm (CohCarrier.GammaH M H) 2, ⇑(T f) = ∑ i, (⇑f) ∣[(2 : ℤ)] A i)
    (hstab : ∀ g : ℍ → ℂ, (∀ γ ∈ GammaHGL M H, g ∣[(0 : ℤ)] γ = g) →
      ∀ γ ∈ GammaHGL M H, (∑ i, g ∣[(0 : ℤ)] A i) ∣[(0 : ℤ)] γ = ∑ i, g ∣[(0 : ℤ)] A i)
    (g : CohCarrier.GammaH M H) :
    T.dualMap (periodOf (CohCarrier.GammaH M H) g) ∈ periodLatticeOf (CohCarrier.GammaH M H) := by
  have hAdet : ∀ i, 0 < ((A i).det : ℝ) := fun i => (hA i).symm ▸ hd
  rw [dualMap_period_eq A hAdet T hT g, ← Submodule.ker_mkQ (periodLatticeOf (CohCarrier.GammaH M H)), LinearMap.mem_ker,
    map_sum]
  simp only [map_sub, Finset.sum_sub_distrib]
  have hmem : ((g : SL(2, ℤ)) : GL (Fin 2) ℝ) ∈ GammaHGL M H :=
    Subgroup.mem_map_of_mem (Matrix.SpecialLinearGroup.mapGL ℝ) g.2
  have := sum_mkQ_Φ_smul_eq A hd hA hstab hmem UpperHalfPlane.I
  simp only [ModularGroup.sl_moeb]
  rw [this, sub_self]

end Engine

section Instances

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ}

private theorem heckeU_eq_sum (k : ℤ) (p : ℕ) (f : ℍ → ℂ) :
    ModularForm.heckeU k p f = ∑ j : Fin p, f ∣[k] ModularForm.heckeMatrix p j := by
  rw [ModularForm.heckeU_def, Finset.sum_range]

private def heckeTFamilyH (M : ℕ) [NeZero M] {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) :
    Option (Fin ℓ) → GL (Fin 2) ℝ :=
  fun o => o.elim
    ((Matrix.SpecialLinearGroup.mapGL ℝ
        ((gammaLift M (unitOfPrimeNotDvd hℓ hℓM) : CongruenceSubgroup.Gamma0 M) :
          SL(2, ℤ)) : GL (Fin 2) ℝ) * ModularForm.heckeDiagMatrix ℓ)
    fun j => ModularForm.heckeMatrix ℓ j

private theorem sum_slash_heckeTFamilyH (k : ℤ) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (f : ℍ → ℂ) :
    ∑ o, f ∣[k] heckeTFamilyH M hℓ hℓM o =
      ModularForm.heckeU k ℓ f +
        f ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ
          ((gammaLift M (unitOfPrimeNotDvd hℓ hℓM) : CongruenceSubgroup.Gamma0 M) :
            SL(2, ℤ)) : GL (Fin 2) ℝ) * ModularForm.heckeDiagMatrix ℓ) := by
  rw [Fintype.sum_option, heckeU_eq_sum, add_comm]
  rfl

private theorem det_heckeTFamilyH {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (o : Option (Fin ℓ)) :
    ((heckeTFamilyH M hℓ hℓM o).det : ℝ) = ℓ := by
  cases o with
  | none =>
    show (((Matrix.SpecialLinearGroup.mapGL ℝ _ : GL (Fin 2) ℝ) * ModularForm.heckeDiagMatrix ℓ).det : ℝ) = ℓ
    rw [map_mul, Units.val_mul, ModularForm.det_heckeDiagMatrix hℓ.ne_zero]
    simp
  | some j => exact ModularForm.det_heckeMatrix hℓ.ne_zero j

private theorem heckeTLinH_dualMap_period_mem {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M)
    (g : CohCarrier.GammaH M H) :
    (CuspForm.heckeTLinH 2 hℓ hℓM).dualMap (periodOf (CohCarrier.GammaH M H) g) ∈
      periodLatticeOf (CohCarrier.GammaH M H) := by
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  refine dualMap_period_mem (heckeTFamilyH M hℓ hℓM) (d := (ℓ : ℝ)) (by exact_mod_cast hℓ.pos)
    (det_heckeTFamilyH hℓ hℓM) _ (fun f => ?_) (fun g hg γ hγ => ?_) g
  · rw [CuspForm.coe_heckeTLinH_apply 2 hℓ hℓM (CuspForm.stableT M H 2 hℓ hℓM), sum_slash_heckeTFamilyH]
  · rw [sum_slash_heckeTFamilyH]
    exact ModularForm.heckeU_add_slash_slash_eq_self_of_mem_GammaH M H 0 hℓ hℓM _
      (gammaLift_apply_11 hℓ hℓM) hg γ hγ

private theorem heckeULinH_dualMap_period_mem {q : ℕ} (hq : q.Prime) (hqM : q ∣ M)
    (g : CohCarrier.GammaH M H) :
    (CuspForm.heckeULinH 2 q).dualMap (periodOf (CohCarrier.GammaH M H) g) ∈
      periodLatticeOf (CohCarrier.GammaH M H) := by
  refine dualMap_period_mem (fun j : Fin q => ModularForm.heckeMatrix q j) (d := (q : ℝ))
    (by exact_mod_cast hq.pos) (fun j => ModularForm.det_heckeMatrix hq.ne_zero j) _
    (fun f => ?_) (fun g hg γ hγ => ?_) g
  · rw [CuspForm.coe_heckeULinH_apply 2 (CuspForm.stableU M H 2 hq hqM), heckeU_eq_sum]
  · rw [← heckeU_eq_sum]
    exact ModularForm.heckeU_slash_eq_self_of_mem_GammaH M H 0 hq hqM hg γ hγ

private theorem diamondLinH_dualMap_period_mem (d : (ZMod M)ˣ) (g : CohCarrier.GammaH M H) :
    (CuspForm.diamondLinH 2 d).dualMap (periodOf (CohCarrier.GammaH M H) g) ∈
      periodLatticeOf (CohCarrier.GammaH M H) := by
  set σ : CongruenceSubgroup.Gamma0 M := gammaLift M d with hσ
  refine dualMap_period_mem (fun _ : Unit => (Matrix.SpecialLinearGroup.mapGL ℝ (σ : SL(2, ℤ)) : GL (Fin 2) ℝ))
    (d := (1 : ℝ)) one_pos (fun _ => by simp) _ (fun f => ?_) (fun g hg γ hγ => ?_) g
  · rw [Fintype.sum_unique, CuspForm.coe_diamondLinH_apply 2 (CuspForm.stableD M H 2)]
  · rw [Fintype.sum_unique]
    obtain ⟨γ₀, hγ₀, rfl⟩ := Subgroup.mem_map.mp hγ
    have hconj : (σ : SL(2, ℤ)) * γ₀ * (σ : SL(2, ℤ))⁻¹ ∈ CohCarrier.GammaH M H :=
      CohCarrier.conj_mem_GammaH M H σ ⟨γ₀, hγ₀⟩
    have e : (Matrix.SpecialLinearGroup.mapGL ℝ (σ : SL(2, ℤ)) : GL (Fin 2) ℝ) *
        (Matrix.SpecialLinearGroup.mapGL ℝ γ₀ : GL (Fin 2) ℝ) =
      (Matrix.SpecialLinearGroup.mapGL ℝ ((σ : SL(2, ℤ)) * γ₀ * (σ : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) *
        (Matrix.SpecialLinearGroup.mapGL ℝ (σ : SL(2, ℤ)) : GL (Fin 2) ℝ) := by
      rw [← map_mul, ← map_mul, inv_mul_cancel_right]
    show (g ∣[(0 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ (σ : SL(2, ℤ)) : GL (Fin 2) ℝ)) ∣[(0 : ℤ)]
        (Matrix.SpecialLinearGroup.mapGL ℝ γ₀ : GL (Fin 2) ℝ) =
      g ∣[(0 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ (σ : SL(2, ℤ)) : GL (Fin 2) ℝ)
    rw [← SlashAction.slash_mul, e, SlashAction.slash_mul, hg _ (Subgroup.mem_map_of_mem _ hconj)]

end Instances

end PeriodLatticeHStableProof

section Final

open PeriodLatticeHStableProof

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)

omit [NeZero M] in
private theorem span_stable (T : Module.Dual ℂ (CuspForm (CohCarrier.GammaH M H) 2) →ₗ[ℂ]
      Module.Dual ℂ (CuspForm (CohCarrier.GammaH M H) 2))
    (hT : ∀ g : CohCarrier.GammaH M H, T (periodOf (CohCarrier.GammaH M H) g) ∈ periodLatticeOf (CohCarrier.GammaH M H)) :
    ∀ v ∈ periodLatticeOf (CohCarrier.GammaH M H), T v ∈ periodLatticeOf (CohCarrier.GammaH M H) := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem _ h =>
    obtain ⟨g, rfl⟩ := h
    exact hT g
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [map_zsmul]; exact Submodule.smul_mem _ a hx

private theorem periodLatticeOf_stable_heckeTLinH {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) :
    ∀ v ∈ periodLatticeOf (CohCarrier.GammaH M H),
      (CuspForm.heckeTLinH 2 hℓ hℓM).dualMap v ∈ periodLatticeOf (CohCarrier.GammaH M H) :=
  span_stable M H _ (heckeTLinH_dualMap_period_mem hℓ hℓM)

private theorem periodLatticeOf_stable_heckeULinH {q : ℕ} (hq : q.Prime) (hqM : q ∣ M) :
    ∀ v ∈ periodLatticeOf (CohCarrier.GammaH M H),
      (CuspForm.heckeULinH 2 q).dualMap v ∈ periodLatticeOf (CohCarrier.GammaH M H) :=
  span_stable M H _ (heckeULinH_dualMap_period_mem hq hqM)

private theorem periodLatticeOf_stable_diamondLinH (d : (ZMod M)ˣ) :
    ∀ v ∈ periodLatticeOf (CohCarrier.GammaH M H),
      (CuspForm.diamondLinH 2 d).dualMap v ∈ periodLatticeOf (CohCarrier.GammaH M H) :=
  span_stable M H _ (diamondLinH_dualMap_period_mem d)

end Final

/-- The period lattice of `Γ_H(M)` is stable under the Hecke operators `T_ℓ`
(`ℓ` prime, `ℓ ∤ M`) and `U_q` (`q ∣ M`) and under the diamond operators, all
acting on the dual through `LinearMap.dualMap`. Stated verbatim from
`Theorems/Thm_ModularCurve_periodLatticeOf_gammaH_heckeDiamondStable.lean`. -/
theorem periodLatticeOf_gammaH_heckeDiamondStable (M : ℕ) [NeZero M]
    (H : Subgroup (ZMod M)ˣ) :
    (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M), ∀ v ∈ periodLatticeOf (CohCarrier.GammaH M H),
        (CuspForm.heckeTLinH 2 hℓ hℓM).dualMap v ∈ periodLatticeOf (CohCarrier.GammaH M H)) ∧
      (∀ (q : ℕ), q.Prime → q ∣ M → ∀ v ∈ periodLatticeOf (CohCarrier.GammaH M H),
        (CuspForm.heckeULinH 2 q).dualMap v ∈ periodLatticeOf (CohCarrier.GammaH M H)) ∧
      (∀ (d : (ZMod M)ˣ), ∀ v ∈ periodLatticeOf (CohCarrier.GammaH M H),
        (CuspForm.diamondLinH 2 d).dualMap v ∈ periodLatticeOf (CohCarrier.GammaH M H)) :=
  ⟨fun _ hℓ hℓM => periodLatticeOf_stable_heckeTLinH M H hℓ hℓM,
    fun _ hq hqM => periodLatticeOf_stable_heckeULinH M H hq hqM,
    fun d => periodLatticeOf_stable_diamondLinH M H d⟩

end ModularCurve

end
