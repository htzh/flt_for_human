/-
  The Hecke-equivariance of `ModularCurve.periodMapOf` under `T_ℓ` and the
  diamond operators.

  Three headlines, verbatim from their `Theorems/` wrappers (pinned `aa2d8b3`):

  - `periodMapOf_gammaH_eq_heckeT_of_coe_eq_heckeU` — `g = U_q f` implies
    `periodMapOf g = heckeT q (periodMapOf f)`, for `q ∣ M`;
  - `periodMapOf_gammaH_eq_diamondRaw_of_coe_eq_slash` — `g = f ∣[2] σ` implies
    `periodMapOf g = diamondRaw σ (periodMapOf f)`;
  - `periodMapOf_gammaH_eq_heckeT_of_coe_eq_heckeU_add_slash` — the same as the
    first with the slash leg `(ρ · diag ℓ)` added, for `ℓ` prime, `ℓ ∤ M`.

  They ride on three engines, all of which are already ported and are imported
  rather than transcribed:

  * node 10, `HeckeEis.coresHom_eq_transfer`
    (`GroupTheory/Corestriction.lean`) — turns the port's `CohCarrier.heckeT`
    (defined as a `MonoidHom.transfer`) into the coset sum
    `∑ c, φ (conjL (transferAux γ c))`;
  * node 11, `Period.IsEquivariantPrimitive.periodHom_eq_of_hasDerivAt`
    (`EichlerShimura/PeriodPrimitive.lean`) — two equivariant primitives with the
    same derivative give the same period hom;
  * node 12 / node 7 (`EichlerShimura/PeriodOf.lean`,
    `EichlerShimura/ExistsEquivariantPrimitive.lean`) — `periodMapOf` at `γ` is
    `periodOf γ`, and `periodOf` is a difference of primitive values.

  The coset decomposition (`beta`, `transl`, `bijective_transl`, `BezoutData`,
  `gammaInf`, `rhoInf`, `bijective_option`, the two `sum_slash_beta_*` sums and
  `mapGL_conjL_mul_heckeMatrix`) is written once, in
  `ModularForms/HeckeCosetDecomposition.lean`; the pin copies it into all four of its
  `S_` files. Here it is only used: node 1's `sum_slash_beta_eq_heckeU` and node
  2's `sum_slash_beta_eq_heckeU_add` are the decomposition's `ℍ → ℂ` versions applied to
  `⇑f` with `SlashInvariantFormClass.slash_action_eq f`, not new lemmas.

  `heckeT_apply_eq_sum`, `periodMapOf_eq_heckeT_of_apply_eq_sum`,
  `hasDerivAt_comp_smul` and `hasDerivAt_moebius` are the pin's proof helpers,
  `private` here — nodes 1 and 2 live in this module, so nothing else needs them.

  Instance/simp walls: the pin's two wrappers open with fifteen
  `attribute [-instance]`/`attribute [-simp]` lines, all about `heckeUpper`,
  `resHom`/`pullbackHom` and `heckeConj`, which the port does not define. All
  fifteen are dropped (decision D4) and none is needed: no proof below mentions
  an instance or simp lemma of `CohCarrier.heckeT`/`conjL`.

  spec-pin: Theorems/Thm_ModularCurve_periodMapOf_gammaH_eq_heckeT_of_coe_eq_heckeU.lean
  spec-pin: P2M/Sol/S_ModularCurve_periodMapOf_gammaH_eq_heckeT_of_coe_eq_heckeU.lean   -- comparable copy
  spec-pin: Theorems/Thm_ModularCurve_periodMapOf_gammaH_eq_diamondRaw_of_coe_eq_slash.lean
  spec-pin: P2M/Sol/S_ModularCurve_periodMapOf_gammaH_eq_diamondRaw_of_coe_eq_slash.lean   -- comparable copy
  spec-pin: Theorems/Thm_ModularCurve_periodMapOf_gammaH_eq_heckeT_of_coe_eq_heckeU_add_slash.lean
  spec-pin: P2M/Sol/S_ModularCurve_periodMapOf_gammaH_eq_heckeT_of_coe_eq_heckeU_add_slash.lean   -- comparable copy
  spec-pin: Theorems/Thm_ModularCurve_periodMapOf_gammaH_eq_comp_of_coe_eq_slash.lean
  spec-pin: P2M/Sol/S_ModularCurve_periodMapOf_gammaH_eq_comp_of_coe_eq_slash.lean   -- comparable copy

  The fourth sibling, `periodMapOf_gammaH_eq_comp_of_coe_eq_slash` (optional,
  plan D6), is included: it is outside the 653 cone, but it shares the family's
  engine and has four outbound citers, and leaving it out would have the next
  wave re-open the family. Its two helpers live in a nested
  `PeriodSlashComp` namespace (as in the pin) because this module already has a
  `private hasDerivAt_comp_smul` with a different binder skeleton.
-/
import FLTForHuman.GroupTheory.Corestriction
import FLTForHuman.ModularForms.Defs.CohCarrierLevel
import FLTForHuman.ModularForms.Defs.GammaH
import FLTForHuman.ModularForms.EichlerShimura.PeriodOf
import FLTForHuman.ModularForms.EichlerShimura.PeriodPrimitive
import FLTForHuman.ModularForms.EichlerShimura.ExistsEquivariantPrimitive
import FLTForHuman.ModularForms.HeckeCosetDecomposition

set_option autoImplicit false

-- The pin's `letI`/`haveI` walls are load-bearing (the coset sum must be
-- definitionally the Hecke operator); kept literal.
set_option linter.style.haveILetI false
-- Node 2's proof is the pin's 6.4M-heartbeat computation.
set_option maxHeartbeats 6400000

noncomputable section

open scoped MatrixGroups ModularForm Topology

open UpperHalfPlane CongruenceSubgroup CohCarrier HeckeCoset Filter
open ModularCurve.Period

namespace ModularCurve

/-! ### The engine: `heckeT` is the coset sum of node 10 -/

private theorem heckeT_apply_eq_sum (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (q : ℕ) [NeZero q]
    {A : Type*} [AddCommGroup A] (φ : H1 M H A) (γ : ↥(GammaH M H)) :
    letI := (GammaHUpper M H q).fintypeQuotientOfFiniteIndex
    heckeT M H q A φ (Additive.ofMul γ) =
      ∑ c : ↥(GammaH M H) ⧸ GammaHUpper M H q,
        φ (Additive.ofMul (conjL M H q (HeckeEis.transferAux (GammaHUpper M H q) γ c))) := by
  have h := HeckeEis.coresHom_eq_transfer (GammaHUpper M H q) (HeckeEis.pullbackHom (conjL M H q) φ)
  show MonoidHom.toAdditiveLeft (MonoidHom.transfer ((AddMonoidHom.toMultiplicativeRight φ).comp
    (conjL M H q))) (Additive.ofMul γ) = _
  rw [show (AddMonoidHom.toMultiplicativeRight φ).comp (conjL M H q) =
      AddMonoidHom.toMultiplicativeRight (HeckeEis.pullbackHom (conjL M H q) φ) from rfl, ← h,
    HeckeEis.coresHom_apply]
  rfl

private theorem hasDerivAt_comp_smul (β : GL (Fin 2) ℝ) (hβ : 0 < β.det.val) {F : ℍ → ℂ} {f : ℍ → ℂ}
    (hF : ∀ w : ℍ, HasDerivAt (F ∘ ofComplex) (f w) ↑w) (τ : ℍ) :
    HasDerivAt (fun z : ℂ => F (β • ofComplex z)) ((f ∣[(2 : ℤ)] β) τ) ↑τ := by

  set a : ℂ := ((β 0 0 : ℝ) : ℂ)
  set b : ℂ := ((β 0 1 : ℝ) : ℂ)
  set c : ℂ := ((β 1 0 : ℝ) : ℂ)
  set d : ℂ := ((β 1 1 : ℝ) : ℂ)
  set moeb : ℂ → ℂ := fun w => (a * w + b) / (c * w + d) with hmoeb
  have hdet : a * d - b * c = ((β.det.val : ℝ) : ℂ) := by
    simp only [a, b, c, d, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
    push_cast; ring
  have hden : ∀ z : ℂ, 0 < z.im → c * z + d ≠ 0 := by
    intro z hz
    have := UpperHalfPlane.denom_ne_zero β (ofComplex z)
    rwa [UpperHalfPlane.denom, ofComplex_apply_of_im_pos hz] at this
  have hmoeb_eq : ∀ z : ℂ, 0 < z.im → ((β • ofComplex z : ℍ) : ℂ) = moeb z := by
    intro z hz
    rw [coe_smul_of_det_pos hβ, UpperHalfPlane.num, UpperHalfPlane.denom, ofComplex_apply_of_im_pos hz]
  have hderiv_moeb : HasDerivAt moeb ((a * d - b * c) / (c * (τ : ℂ) + d) ^ 2) (τ : ℂ) := by
    have hnum : HasDerivAt (fun w : ℂ => a * w + b) a (τ : ℂ) := by
      simpa using ((hasDerivAt_id (τ : ℂ)).const_mul a).add_const b
    have hden' : HasDerivAt (fun w : ℂ => c * w + d) c (τ : ℂ) := by
      simpa using ((hasDerivAt_id (τ : ℂ)).const_mul c).add_const d
    have h := hnum.div hden' (hden _ τ.2)
    convert h using 1; try rfl
    ring
  have hev : (fun z : ℂ => F (β • ofComplex z)) =ᶠ[𝓝 (τ : ℂ)] (fun z : ℂ => (F ∘ ofComplex) (moeb z)) := by
    have hopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
    filter_upwards [hopen.mem_nhds τ.2] with z hz
    simp only [Function.comp_apply]
    rw [← hmoeb_eq z hz, ofComplex_apply]
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  have h1 : HasDerivAt (F ∘ ofComplex) (f (β • τ)) (moeb (τ : ℂ)) := by
    have := hF (β • τ)
    rwa [show ((β • τ : ℍ) : ℂ) = moeb (τ : ℂ) from by
      rw [← hmoeb_eq (τ : ℂ) τ.2, ofComplex_apply]] at this
  have h := h1.comp (τ : ℂ) hderiv_moeb

  have hval : (f ∣[(2 : ℤ)] β) τ = f (β • τ) * ((a * d - b * c) / (c * (τ : ℂ) + d) ^ 2) := by
    rw [ModularForm.slash_apply, UpperHalfPlane.σ, ite_eq_left hβ, hdet]
    simp only [ContinuousAlgEquiv.refl_apply, abs_of_pos hβ]
    rw [show ((2 : ℤ) - 1) = 1 by norm_num, zpow_one, UpperHalfPlane.denom, zpow_neg, zpow_two, div_eq_mul_inv,
      pow_two, mul_assoc]
  rw [hval]
  exact h

/-! ### The shared step of nodes 1 and 2 -/

private theorem periodMapOf_eq_heckeT_of_apply_eq_sum (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (q : ℕ) [NeZero q] (f g : CuspForm (GammaH M H) 2)
    (hsum : letI := (GammaHUpper M H q).fintypeQuotientOfFiniteIndex
      ∀ τ : ℍ, g τ = ∑ c : ↥(GammaH M H) ⧸ GammaHUpper M H q, (⇑f ∣[(2 : ℤ)] beta M H q c) τ) :
    periodMapOf (GammaH M H) g = heckeT M H q ℂ (periodMapOf (GammaH M H) f) := by
  letI := (GammaHUpper M H q).fintypeQuotientOfFiniteIndex

  obtain ⟨F₀, hF₀⟩ := exists_hasEquivariantPrimitiveOf (GammaH M H) f
  obtain ⟨F, hF, hdefF⟩ := periodMapOf_def (GammaH M H) f hF₀
  obtain ⟨G₀, hG₀⟩ := exists_hasEquivariantPrimitiveOf (GammaH M H) g
  obtain ⟨G, hG, hdefG⟩ := periodMapOf_def (GammaH M H) g hG₀
  have hFd := hF.1
  have hFeq := hF.2.2.1

  set Φ : ℍ → ℂ := fun z => ∑ c : ↥(GammaH M H) ⧸ GammaHUpper M H q, F (beta M H q c • z) with hΦ

  have hbeta : ∀ (γ : ↥(GammaH M H)) (d : ↥(GammaH M H) ⧸ GammaHUpper M H q) (z : ℍ),
      beta M H q (γ • d) • ((γ : SL(2, ℤ)) • z) =
        ((conjL M H q (HeckeEis.transferAux (GammaHUpper M H q) γ d) : ↥(GammaH M H)) : SL(2, ℤ)) •
          (beta M H q d • z) := by
    intro γ d z
    set t := HeckeEis.transferAux (GammaHUpper M H q) γ d with ht
    have hrel : (((γ • d).out : ↥(GammaH M H)) : SL(2, ℤ))⁻¹ * (γ : SL(2, ℤ)) =
        ((t : ↥(GammaH M H)) : SL(2, ℤ)) * (((d.out : ↥(GammaH M H)) : SL(2, ℤ)))⁻¹ := by
      have : ((t : ↥(GammaH M H)) : SL(2, ℤ)) =
          (((γ • d).out : ↥(GammaH M H)) : SL(2, ℤ))⁻¹ *
            ((γ : SL(2, ℤ)) * ((d.out : ↥(GammaH M H)) : SL(2, ℤ))) := rfl
      rw [this]; group
    show beta M H q (γ • d) • ((Matrix.SpecialLinearGroup.mapGL ℝ (γ : SL(2, ℤ)) : GL (Fin 2) ℝ) • z) =
      (Matrix.SpecialLinearGroup.mapGL ℝ ((conjL M H q t : ↥(GammaH M H)) : SL(2, ℤ)) : GL (Fin 2) ℝ) •
        (beta M H q d • z)
    rw [← mul_smul, ← mul_smul]
    congr 1
    simp only [beta]
    rw [mul_assoc, ← map_mul, hrel, map_mul, ← mul_assoc, ← mapGL_conjL_mul_heckeMatrix, mul_assoc]

  have hcob : ∀ (γ : ↥(GammaH M H)) (z : ℍ),
      Φ ((γ : SL(2, ℤ)) • z) - Φ z = heckeT M H q ℂ hFeq.periodHom (Additive.ofMul γ) := by
    intro γ z
    simp only [hΦ]
    rw [heckeT_apply_eq_sum,
      ← Fintype.sum_bijective (γ • ·) (MulAction.bijective γ)
        (fun d => F (beta M H q (γ • d) • ((γ : SL(2, ℤ)) • z)))
        (fun c => F (beta M H q c • ((γ : SL(2, ℤ)) • z))) (fun d => rfl),
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [hbeta γ d z, IsEquivariantPrimitive.periodHom_apply, ← hFeq.sub_eq_period _ (beta M H q d • z)]
  have hΦeq : IsEquivariantPrimitive (GammaH M H) Φ := fun γ => ⟨_, hcob γ⟩

  have hbdet : ∀ c : ↥(GammaH M H) ⧸ GammaHUpper M H q, 0 < (beta M H q c).det.val := by
    intro c
    simp only [beta, map_mul, Units.val_mul]
    refine mul_pos (ModularForm.det_heckeMatrix_pos q 0) ?_
    have : ((Matrix.GeneralLinearGroup.det
        (Matrix.SpecialLinearGroup.mapGL ℝ (((c.out : ↥(GammaH M H)) : SL(2, ℤ))⁻¹))).val : ℝ) = 1 := by
      rw [Matrix.GeneralLinearGroup.val_det_apply]
      exact Matrix.SpecialLinearGroup.det_coe _
    rw [this]; exact one_pos
  have hΦd : ∀ τ : ℍ, HasDerivAt (Φ ∘ ofComplex) (g τ) ↑τ := by
    intro τ
    rw [hsum τ]
    have := HasDerivAt.sum (u := Finset.univ)
      (fun (c : ↥(GammaH M H) ⧸ GammaHUpper M H q) _ => hasDerivAt_comp_smul (beta M H q c) (hbdet c) hFd τ)
    convert this using 1; try rfl
    ext z
    simp only [Function.comp_apply, hΦ, Finset.sum_apply]

  rw [hdefG, hdefF, hG.2.2.1.periodHom_eq_of_hasDerivAt hΦeq hG.1 hΦd]
  refine AddMonoidHom.ext fun x => ?_
  induction x using Additive.rec with
  | ofMul γ =>
  rw [IsEquivariantPrimitive.periodHom_apply, ← hΦeq.sub_eq_period γ UpperHalfPlane.I, hcob γ]

/-! ### Node 1: `T`-equivariance through the `U` leg -/

theorem periodMapOf_gammaH_eq_heckeT_of_coe_eq_heckeU
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) {q : ℕ} (hq : q.Prime) (hqM : q ∣ M)
    (f g : CuspForm (CohCarrier.GammaH M H) 2)
    (hg : ⇑g = ModularForm.heckeU 2 q ⇑f) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    ModularCurve.periodMapOf (CohCarrier.GammaH M H) g =
      CohCarrier.heckeT M H q ℂ (ModularCurve.periodMapOf (CohCarrier.GammaH M H) f) := by
  haveI : NeZero q := ⟨hq.ne_zero⟩
  apply periodMapOf_eq_heckeT_of_apply_eq_sum M H q f g
  intro τ
  letI := (GammaHUpper M H q).fintypeQuotientOfFiniteIndex
  rw [hg, ← sum_slash_beta_eq_heckeU M H q hqM 2
      (fun γ hγ => SlashInvariantFormClass.slash_action_eq f γ hγ), Finset.sum_apply]

/-! ### Node 3: the diamond operator -/

private theorem hasDerivAt_moebius (s : SL(2, ℤ)) (z : ℂ) (hz : ((s 1 0 : ℤ) : ℂ) * z + ((s 1 1 : ℤ) : ℂ) ≠ 0) :
    HasDerivAt (fun w : ℂ => (((s 0 0 : ℤ) : ℂ) * w + ((s 0 1 : ℤ) : ℂ)) / (((s 1 0 : ℤ) : ℂ) * w + ((s 1 1 : ℤ) : ℂ)))
      (1 / (((s 1 0 : ℤ) : ℂ) * z + ((s 1 1 : ℤ) : ℂ)) ^ 2) z := by
  have hnum : HasDerivAt (fun w : ℂ => ((s 0 0 : ℤ) : ℂ) * w + ((s 0 1 : ℤ) : ℂ)) ((s 0 0 : ℤ) : ℂ) z := by
    simpa using ((hasDerivAt_id z).const_mul ((s 0 0 : ℤ) : ℂ)).add_const ((s 0 1 : ℤ) : ℂ)
  have hden : HasDerivAt (fun w : ℂ => ((s 1 0 : ℤ) : ℂ) * w + ((s 1 1 : ℤ) : ℂ)) ((s 1 0 : ℤ) : ℂ) z := by
    simpa using ((hasDerivAt_id z).const_mul ((s 1 0 : ℤ) : ℂ)).add_const ((s 1 1 : ℤ) : ℂ)
  have h := hnum.div hden hz
  have hdet : ((s 0 0 : ℤ) : ℂ) * ((s 1 1 : ℤ) : ℂ) - ((s 0 1 : ℤ) : ℂ) * ((s 1 0 : ℤ) : ℂ) = 1 := by
    have := Matrix.SpecialLinearGroup.det_coe s
    rw [Matrix.det_fin_two] at this
    exact_mod_cast this
  convert h using 1
  rw [one_div, eq_div_iff (pow_ne_zero 2 hz), inv_mul_cancel₀ (pow_ne_zero 2 hz)]
  linear_combination -hdet

theorem periodMapOf_gammaH_eq_diamondRaw_of_coe_eq_slash
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (σ : CongruenceSubgroup.Gamma0 M)
    (f g : CuspForm (CohCarrier.GammaH M H) 2)
    (hg : ⇑g = ⇑f ∣[(2 : ℤ)] ((Matrix.SpecialLinearGroup.mapGL ℝ (σ : SL(2, ℤ)) : GL (Fin 2) ℝ))) :
    ModularCurve.periodMapOf (CohCarrier.GammaH M H) g =
      CohCarrier.diamondRaw M H ℂ σ (ModularCurve.periodMapOf (CohCarrier.GammaH M H) f) := by
  obtain ⟨F, hFd, hF0, hFeq, hFcusp⟩ := exists_hasEquivariantPrimitiveOf (GammaH M H) f
  set s : SL(2, ℤ) := (σ : SL(2, ℤ)) with hs
  obtain ⟨L, hL⟩ := hFcusp s

  have hconj : ∀ (γ : ↥(GammaH M H)) (z : ℍ),
      s • ((γ : SL(2, ℤ)) • z) = ((conjHom M H σ γ : ↥(GammaH M H)) : SL(2, ℤ)) • (s • z) := by
    intro γ z
    rw [← mul_smul, ← mul_smul]
    congr 1
    show s * (γ : SL(2, ℤ)) = (σ : SL(2, ℤ)) * (γ : SL(2, ℤ)) * (σ : SL(2, ℤ))⁻¹ * s
    rw [hs, inv_mul_cancel_right]

  set G : ℍ → ℂ := fun w => F (s • w) - L with hG
  have hGeq : IsEquivariantPrimitive (GammaH M H) G := by
    intro γ
    obtain ⟨c, hc⟩ := hFeq (conjHom M H σ γ)
    refine ⟨c, fun z => ?_⟩
    simp only [hG]
    rw [hconj γ z, sub_sub_sub_cancel_right]
    exact hc (s • z)
  have hG0 : Tendsto G atImInfty (𝓝 0) := by
    have := hL.sub_const L
    rwa [sub_self] at this
  have hGcusp : ∀ δ : SL(2, ℤ), ∃ L' : ℂ, Tendsto (fun w : ℍ => G (δ • w)) atImInfty (𝓝 L') := by
    intro δ
    obtain ⟨L', hL'⟩ := hFcusp (s * δ)
    refine ⟨L' - L, ?_⟩
    have : (fun w : ℍ => G (δ • w)) = fun w => F ((s * δ) • w) - L := by
      ext w; simp only [hG, mul_smul]
    rw [this]
    exact hL'.sub_const L
  have hGd : ∀ τ : ℍ, HasDerivAt (G ∘ ofComplex) (g τ) ↑τ := by
    intro τ

    have hden : ∀ z : ℂ, 0 < z.im → ((s 1 0 : ℤ) : ℂ) * z + ((s 1 1 : ℤ) : ℂ) ≠ 0 := by
      intro z hz h0
      have := congrArg Complex.im h0
      simp only [Complex.add_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im, zero_mul, add_zero,
        Complex.zero_im] at this

      have h10 : ((s 1 0 : ℤ) : ℝ) = 0 := by
        rcases mul_eq_zero.mp this with h | h
        · exact h
        · exact absurd h hz.ne'
      have h11 : ((s 1 1 : ℤ) : ℂ) = 0 := by
        have := congrArg Complex.re h0
        simp only [Complex.add_re, Complex.mul_re, Complex.intCast_re, Complex.intCast_im, zero_mul, sub_zero,
          Complex.zero_re] at this
        have h10' : ((s 1 0 : ℤ) : ℝ) * z.re = 0 := by rw [h10, zero_mul]
        rw [h10', zero_add] at this
        exact_mod_cast this
      have hdet := Matrix.SpecialLinearGroup.det_coe s
      rw [Matrix.det_fin_two] at hdet
      have h10z : (s 1 0 : ℤ) = 0 := by exact_mod_cast h10
      have h11z : (s 1 1 : ℤ) = 0 := by exact_mod_cast h11
      rw [h10z, h11z, mul_zero, mul_zero, sub_zero] at hdet
      exact zero_ne_one hdet
    have hdenom : denom (Matrix.SpecialLinearGroup.toGL ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) s))
        (τ : ℂ) = ((s 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((s 1 1 : ℤ) : ℂ) := by
      simp [UpperHalfPlane.denom]
    have hval : g τ = f (s • τ) * (1 / (((s 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((s 1 1 : ℤ) : ℂ)) ^ 2) := by
      have := congrFun hg τ
      rw [this]
      show (⇑f ∣[(2 : ℤ)] s) τ = _
      rw [ModularForm.SL_slash_apply, hdenom, zpow_neg, zpow_two, one_div, pow_two]
    rw [hval]

    set moeb : ℂ → ℂ := fun w =>
      (((s 0 0 : ℤ) : ℂ) * w + ((s 0 1 : ℤ) : ℂ)) / (((s 1 0 : ℤ) : ℂ) * w + ((s 1 1 : ℤ) : ℂ)) with hmoeb
    have hmoeb_eq : ∀ z : ℂ, 0 < z.im → ((s • ofComplex z : ℍ) : ℂ) = moeb z := by
      intro z hz
      rw [coe_specialLinearGroup_apply, ofComplex_apply_of_im_pos hz]
      simp [hmoeb]
    have hev : (G ∘ ofComplex) =ᶠ[𝓝 (τ : ℂ)] (fun z : ℂ => (F ∘ ofComplex) (moeb z) - L) := by
      have hopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
      filter_upwards [hopen.mem_nhds τ.2] with z hz
      simp only [Function.comp_apply, hG]
      rw [← hmoeb_eq z hz, ofComplex_apply]
    refine HasDerivAt.congr_of_eventuallyEq ?_ hev
    have h1 : HasDerivAt (F ∘ ofComplex) (f (s • τ)) (moeb (τ : ℂ)) := by
      have := hFd (s • τ)
      rwa [show ((s • τ : ℍ) : ℂ) = moeb (τ : ℂ) from by
        rw [← hmoeb_eq (τ : ℂ) τ.2, ofComplex_apply]] at this
    have h2 := hasDerivAt_moebius s (τ : ℂ) (hden _ τ.2)
    exact (h1.comp (τ : ℂ) h2).sub_const L

  refine AddMonoidHom.ext fun x => ?_
  induction x using Additive.rec with
  | ofMul γ =>
  show periodMapOf (GammaH M H) g (Additive.ofMul γ) =
    periodMapOf (GammaH M H) f (Additive.ofMul (conjHom M H σ γ))
  rw [periodMapOf_apply_eq_periodOf, periodMapOf_apply_eq_periodOf,
    periodOf_apply_eq_sub_of_hasEquivariantPrimitiveOf _ g ⟨hGd, hG0, hGeq, hGcusp⟩,
    periodOf_apply_eq_sub_of_hasEquivariantPrimitiveOf _ f ⟨hFd, hF0, hFeq, hFcusp⟩]
  obtain ⟨c, hc⟩ := hFeq (conjHom M H σ γ)
  simp only [hG]
  rw [hconj γ, sub_sub_sub_cancel_right, hc (s • UpperHalfPlane.I), ← hc UpperHalfPlane.I]

/-! ### Node 2: the same with the slash leg `(ρ · diag ℓ)` -/

/-- The decomposition's `sum_slash_beta_eq_heckeU_add` at `k = 2` and `f : CuspForm _ 2`,
whose `Γ_H`-invariance is `SlashInvariantFormClass.slash_action_eq`. -/
private theorem sum_slash_beta_eq_heckeU_add_cuspForm (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (ℓ : ℕ) [Fact ℓ.Prime] (B : BezoutData M ℓ) (ρ : Gamma0 M)
    (hρ : (((ρ : SL(2, ℤ)) 1 1 : ℤ) : ZMod M) = ℓ) (f : CuspForm (GammaH M H) 2) :
    letI := (GammaHUpper M H ℓ).fintypeQuotientOfFiniteIndex
    (∑ c : ↥(GammaH M H) ⧸ GammaHUpper M H ℓ, ⇑f ∣[(2 : ℤ)] beta M H ℓ c) =
      ModularForm.heckeU 2 ℓ ⇑f +
        (⇑f ∣[(2 : ℤ)] ((Matrix.SpecialLinearGroup.mapGL ℝ (ρ : SL(2, ℤ)) : GL (Fin 2) ℝ) *
          ModularForm.heckeDiagMatrix ℓ)) :=
  sum_slash_beta_eq_heckeU_add H B ρ hρ 2
    (fun γ hγ => SlashInvariantFormClass.slash_action_eq f γ hγ)

theorem periodMapOf_gammaH_eq_heckeT_of_coe_eq_heckeU_add_slash
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M)
    (ρ : CongruenceSubgroup.Gamma0 M)
    (hρ : (((ρ : SL(2, ℤ)) 1 1 : ℤ) : ZMod M) = ℓ)
    (f g : CuspForm (CohCarrier.GammaH M H) 2)
    (hg : ⇑g = ModularForm.heckeU 2 ℓ ⇑f +
      (⇑f ∣[(2 : ℤ)] ((Matrix.SpecialLinearGroup.mapGL ℝ (ρ : SL(2, ℤ)) : GL (Fin 2) ℝ) *
        ModularForm.heckeDiagMatrix ℓ))) :
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    ModularCurve.periodMapOf (CohCarrier.GammaH M H) g =
      CohCarrier.heckeT M H ℓ ℂ (ModularCurve.periodMapOf (CohCarrier.GammaH M H) f) := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨B⟩ := exists_bezoutData M ℓ hℓM
  apply periodMapOf_eq_heckeT_of_apply_eq_sum M H ℓ f g
  intro τ
  letI := (GammaHUpper M H ℓ).fintypeQuotientOfFiniteIndex
  rw [hg, ← sum_slash_beta_eq_heckeU_add_cuspForm M H ℓ B ρ hρ f, Finset.sum_apply]

/-! ### The optional fourth sibling: `comp` along a matrix conjugating `Γ_H` -/

namespace PeriodSlashComp

private theorem sub_eq_sub_of_hasDerivAt {Φ Ψ : ℍ → ℂ} {φ : ℍ → ℂ}
    (hΦ : ∀ τ : ℍ, HasDerivAt (Φ ∘ ofComplex) (φ τ) ↑τ)
    (hΨ : ∀ τ : ℍ, HasDerivAt (Ψ ∘ ofComplex) (φ τ) ↑τ) (z w : ℍ) :
    Φ z - Φ w = Ψ z - Ψ w := by
  set D : ℂ → ℂ := fun x => (Φ ∘ ofComplex) x - (Ψ ∘ ofComplex) x with hD
  have hDer : ∀ x ∈ upperHalfPlaneSet, HasDerivAt D 0 x := by
    intro x hx
    have h := (hΦ ⟨x, hx⟩).sub (hΨ ⟨x, hx⟩)
    rw [sub_self] at h
    exact h
  have hdiff : DifferentiableOn ℂ D upperHalfPlaneSet :=
    fun x hx => (hDer x hx).differentiableAt.differentiableWithinAt
  have hderiv : Set.EqOn (deriv D) 0 upperHalfPlaneSet := fun x hx => (hDer x hx).deriv
  have hpre : IsPreconnected upperHalfPlaneSet := (convex_halfSpace_im_gt 0).isPreconnected
  have key := isOpen_upperHalfPlaneSet.is_const_of_deriv_eq_zero hpre hdiff hderiv z.im_pos w.im_pos
  simp only [hD, Function.comp_apply, ofComplex_apply] at key
  linear_combination key

private theorem hasDerivAt_comp_smul {F f : ℍ → ℂ} {α : GL (Fin 2) ℝ}
    (hα : 0 < ((Matrix.GeneralLinearGroup.det α : ℝˣ) : ℝ))
    (hF : ∀ τ : ℍ, HasDerivAt (F ∘ ofComplex) (f τ) ↑τ) (τ : ℍ) :
    HasDerivAt ((fun w : ℍ => F (α • w)) ∘ ofComplex) ((f ∣[(2 : ℤ)] α) τ) ↑τ := by
  have hα' : 0 < α.val.det := by rwa [Matrix.GeneralLinearGroup.val_det_apply] at hα
  have h1 : HasDerivAt (F ∘ ofComplex) (f (α • τ)) ↑(α • τ) := hF (α • τ)
  have h2 : HasDerivAt (fun z : ℂ => (↑(α • ofComplex z) : ℂ)) (α.val.det / denom α τ ^ 2) ↑τ :=
    (UpperHalfPlane.hasStrictDerivAt_smul hα' τ).hasDerivAt
  have h3 := h1.comp_of_eq (↑τ : ℂ) h2 (by simp only [ofComplex_apply])
  have hfun : (F ∘ ofComplex) ∘ (fun z : ℂ => (↑(α • ofComplex z) : ℂ)) =
      (fun w : ℍ => F (α • w)) ∘ ofComplex := by
    funext z
    simp only [Function.comp_apply, ofComplex_apply]
  rw [hfun] at h3
  convert h3 using 1; try with_reducible_and_instances rfl
  rw [ModularForm.slash_apply]
  have hσ : UpperHalfPlane.σ α = ContinuousAlgEquiv.refl ℝ ℂ := by
    simp only [UpperHalfPlane.σ, hα, ite_true]
  have habs : |((Matrix.GeneralLinearGroup.det α : ℝˣ) : ℝ)| = α.val.det := by
    rw [abs_of_pos hα, Matrix.GeneralLinearGroup.val_det_apply]
  rw [hσ, habs, ContinuousAlgEquiv.refl_apply]
  have hden : denom α (↑τ : ℂ) ≠ 0 := denom_ne_zero α τ
  rw [show ((2 : ℤ) - 1) = 1 from by norm_num, zpow_one, zpow_neg, zpow_ofNat]
  field_simp

end PeriodSlashComp

theorem periodMapOf_gammaH_eq_comp_of_coe_eq_slash
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (α : GL (Fin 2) ℝ)
    (hα : 0 < ((Matrix.GeneralLinearGroup.det α : ℝˣ) : ℝ))
    (c : ↥(CohCarrier.GammaH M H) →* ↥(CohCarrier.GammaH M H))
    (hc : ∀ δ : ↥(CohCarrier.GammaH M H),
      (((c δ : ↥(CohCarrier.GammaH M H)) : SL(2, ℤ)) : GL (Fin 2) ℝ) = α * ((δ : SL(2, ℤ)) : GL (Fin 2) ℝ) * α⁻¹)
    (f g : CuspForm (CohCarrier.GammaH M H) 2) (hg : ⇑g = ⇑f ∣[(2 : ℤ)] α) :
    ModularCurve.periodMapOf (CohCarrier.GammaH M H) g =
      (ModularCurve.periodMapOf (CohCarrier.GammaH M H) f).comp (MonoidHom.toAdditive c) := by
  obtain ⟨F, hF⟩ := ModularCurve.exists_hasEquivariantPrimitiveOf (CohCarrier.GammaH M H) f
  obtain ⟨F₀, hF₀, hpf⟩ := ModularCurve.periodMapOf_def (CohCarrier.GammaH M H) f hF
  obtain ⟨G, hG⟩ := ModularCurve.exists_hasEquivariantPrimitiveOf (CohCarrier.GammaH M H) g
  obtain ⟨G₀, hG₀, hpg⟩ := ModularCurve.periodMapOf_def (CohCarrier.GammaH M H) g hG
  rw [hpf, hpg]
  refine AddMonoidHom.ext fun x => ?_
  obtain ⟨δ, rfl⟩ : ∃ δ : ↥(CohCarrier.GammaH M H), Additive.ofMul δ = x := ⟨Additive.toMul x, rfl⟩
  show hG₀.2.2.1.periodHom (Additive.ofMul δ) = hF₀.2.2.1.periodHom (Additive.ofMul (c δ))
  rw [ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply,
    ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply]
  show G₀ ((δ : SL(2, ℤ)) • UpperHalfPlane.I) - G₀ UpperHalfPlane.I =
    F₀ (((c δ : ↥(CohCarrier.GammaH M H)) : SL(2, ℤ)) • UpperHalfPlane.I) - F₀ UpperHalfPlane.I

  have hconj : ∀ w : ℍ, ((c δ : ↥(CohCarrier.GammaH M H)) : SL(2, ℤ)) • (α • w) = α • ((δ : SL(2, ℤ)) • w) := by
    intro w
    rw [ModularGroup.sl_moeb, ModularGroup.sl_moeb]
    rw [hc δ, smul_smul, inv_mul_cancel_right, mul_smul]

  have hbase : F₀ (((c δ : ↥(CohCarrier.GammaH M H)) : SL(2, ℤ)) • UpperHalfPlane.I) - F₀ UpperHalfPlane.I =
      F₀ (α • ((δ : SL(2, ℤ)) • UpperHalfPlane.I)) - F₀ (α • UpperHalfPlane.I) := by
    have h1 := hF₀.2.2.1.sub_eq_period (c δ) (α • UpperHalfPlane.I)
    have h2 := hF₀.2.2.1.sub_eq_period (c δ) UpperHalfPlane.I
    rw [hconj] at h1
    rw [h2, ← h1]

  have hΨ : ∀ τ : ℍ, HasDerivAt ((fun w : ℍ => F₀ (α • w)) ∘ ofComplex) (g τ) ↑τ := by
    intro τ
    rw [show g τ = (⇑f ∣[(2 : ℤ)] α) τ from congrFun hg τ]
    exact PeriodSlashComp.hasDerivAt_comp_smul hα hF₀.1 τ
  rw [hbase]
  exact PeriodSlashComp.sub_eq_sub_of_hasDerivAt hG₀.1 hΨ _ _

end ModularCurve

end
