/-
  The general Eisenstein series `EisensteinSeries.eisensteinG`, its canonical
  `SlashInvariantForm`/`ModularForm` bundles, and the two headlines it was ported
  for: modularity (`exists_modularForm_coe_eq_eisensteinG`) and the divisor-sum
  formula for its `q`-expansion (`qExpansion_eisensteinG_coeff`).

  This module is not weight-one-specific: `eisensteinG` is general in the weight
  `k : ℤ`, the level `N` and the residue class `a`, so it lives at the
  `ModularForms/` root rather than under `WeightOne/` (SET-5 ported it as the
  Eisenstein input of the route-C' weight-one effort, which is why the pin's
  filenames are `S_EisensteinSeries_*`).

  The definition is transcribed from
  `Definitions/Def_EisensteinSeries_EisensteinG.lean`; the statements are the
  pinned wrappers `Theorems/Thm_EisensteinSeries_*.lean` verbatim, and the proofs
  are ported from the matching `P2M/Sol/S_EisensteinSeries_*.lean`, adapted to
  mathlib `v4.34.0`. The general API (`congrSet`, `eisensteinGSIF`,
  `eisensteinGMF`, the slash/analytic lemmas, the `cls` residue-class vocabulary,
  ...) is public: it is the reusable interface of the series. The pin keeps the
  same block inside its `P2MW.S_...CardG1`/`CardC` implementation namespaces, so
  `spec/check_flt_statements.py` still diffs every public statement against the
  pin's copies.

  Why mathlib's Eisenstein API is not reused: mathlib's `eisensteinSeries` sums
  `eisSummand` over the *primitive* pairs in a congruence class (`gammaSet N 1 a`,
  `gcd = 1`), while `eisensteinG` sums over the *whole* class (`congrSet N a`).
  The two differ already at level `1`, where the full sum is `riemannZeta k` times
  the primitive one (`EisensteinSeries.tsum_eisSummand_eq_riemannZeta_mul_eisensteinSeries`).
  So the modularity block is a re-derivation -- structurally the same as mathlib's
  `eisensteinSeriesSIF`/`eisensteinSeriesMF` chain, but against the unrestricted
  congruence class, and it cannot be replaced by it. Mathlib's only Eisenstein
  `q`-expansion is the level-one, even-weight `E_qExpansion_coeff`, so the
  coefficient formula here is new; the analytic input it does use is mathlib's
  `EisensteinSeries.qExpansion_identity_pnat`.
-/

import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Summable
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.UniformConvergence
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.MDifferentiable
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.IsBoundedAtImInfty
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import FLTForHuman.ModularForms.Defs.ResidueClass
import FLTForHuman.ModularForms.Defs.SlashActions
import FLTForHuman.ModularForms.Defs.TsumDivisorsAntidiagonal

set_option autoImplicit false
set_option linter.style.haveILetI false

open scoped MatrixGroups CongruenceSubgroup ModularForm Topology Manifold Matrix Nat
open UpperHalfPlane hiding I
open Filter Complex Real
open ResidueClass SlashAction

noncomputable section

namespace EisensteinSeries

/-- The general Eisenstein series of weight `k` and level `N`, indexed by the
residue class `a`. Transcribed from the pin's definition file. -/
noncomputable def eisensteinG (N : ℕ) (k : ℤ) (a : Fin 2 → ZMod N) (z : UpperHalfPlane) : ℂ :=
  ∑' v : {v : Fin 2 → ℤ // ((↑) : ℤ → ZMod N) ∘ v = a}, eisSummand k v.1 z

variable {N : ℕ} {k : ℤ}

/-! ### The index set and the `SL(2, ℤ)`-action -/

/-- The integer vectors whose image in `(ZMod N)²` is `a`: the index set of
`eisensteinG`. -/
def congrSet (N : ℕ) (a : Fin 2 → ZMod N) : Set (Fin 2 → ℤ) := {v | ((↑) : ℤ → ZMod N) ∘ v = a}

lemma eisensteinG_eq (N : ℕ) (k : ℤ) (a : Fin 2 → ZMod N) :
    EisensteinSeries.eisensteinG N k a = fun z => ∑' v : congrSet N a, eisSummand k v z := rfl

lemma vecMul_mem_congrSet {a : Fin 2 → ZMod N} {v : Fin 2 → ℤ} (hv : v ∈ congrSet N a)
    (γ : SL(2, ℤ)) : v ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ) ∈ congrSet N (a ᵥ* γ) := by
  simp only [congrSet, Set.mem_ofPred_eq] at hv ⊢
  have := RingHom.map_vecMul (m := Fin 2) (n := Fin 2) (Int.castRingHom (ZMod N)) γ v
  simp only [eq_intCast, Int.coe_castRingHom] at this
  simp_rw [Function.comp_def, this, ← hv]
  rfl

/-- The `SL(2, ℤ)`-action on the congruence class, by right multiplication. -/
def congrSetEquiv (a : Fin 2 → ZMod N) (γ : SL(2, ℤ)) : congrSet N a ≃ congrSet N (a ᵥ* γ) where
  toFun v := ⟨v.1 ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ), vecMul_mem_congrSet v.2 γ⟩
  invFun v := ⟨v.1 ᵥ* ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ), by
      have := vecMul_mem_congrSet v.2 γ⁻¹
      rw [Matrix.vecMul_vecMul, ← Matrix.SpecialLinearGroup.coe_mul] at this
      simpa only [map_inv, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.vecMul_one]
        using this⟩
  left_inv v := by simp_rw [Matrix.vecMul_vecMul, ← Matrix.SpecialLinearGroup.coe_mul,
    mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.vecMul_one]
  right_inv v := by simp_rw [Matrix.vecMul_vecMul, ← Matrix.SpecialLinearGroup.coe_mul,
    inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.vecMul_one]

theorem eisensteinG_slash_apply (N : ℕ) (k : ℤ) (a : Fin 2 → ZMod N) (γ : SL(2, ℤ)) :
    EisensteinSeries.eisensteinG N k a ∣[k] γ = EisensteinSeries.eisensteinG N k (a ᵥ* γ) := by
  ext1 z
  simp_rw [ModularForm.SL_slash_apply, zpow_neg,
    mul_inv_eq_iff_eq_mul₀ (zpow_ne_zero _ <| denom_ne_zero _ z), eisensteinG_eq,
    eisSummand_SL2_apply, tsum_mul_left, mul_comm (_ ^ k)]
  congr 1
  exact (congrSetEquiv a γ).tsum_eq (fun v => eisSummand k v z)

/-! ### Slash-invariant form, modular form, and the analytic API -/

/-- `eisensteinG` as a slash-invariant form on `Γ(N)`. -/
noncomputable def eisensteinGSIF (N : ℕ) (k : ℤ) (a : Fin 2 → ZMod N) : SlashInvariantForm Γ(N) k where
  toFun := EisensteinSeries.eisensteinG N k a
  slash_action_eq' A hA := by
    obtain ⟨A, (hA : A ∈ Γ(N)), rfl⟩ := hA
    simp [Matrix.SpecialLinearGroup.mapGL, ← ModularForm.SL_slash, eisensteinG_slash_apply,
      CongruenceSubgroup.Gamma_mem'.mp hA]

lemma eisensteinGSIF_apply (N : ℕ) (k : ℤ) (a : Fin 2 → ZMod N) (z : ℍ) :
    eisensteinGSIF N k a z = EisensteinSeries.eisensteinG N k a z := rfl

lemma coe_eisensteinGSIF (N : ℕ) (k : ℤ) (a : Fin 2 → ZMod N) :
    ⇑(eisensteinGSIF N k a) = EisensteinSeries.eisensteinG N k a := rfl

theorem eisensteinG_tendstoLocallyUniformly (hk : 3 ≤ k) (a : Fin 2 → ZMod N) :
    TendstoLocallyUniformly (fun (s : Finset (congrSet N a)) => (∑ x ∈ s, eisSummand k x ·))
      (EisensteinSeries.eisensteinG N k a ·) Filter.atTop := by
  have hk' : (2 : ℝ) < k := by norm_cast
  have p_sum : Summable fun x : congrSet N a => ‖x.val‖ ^ (-k) :=
    mod_cast (summable_one_div_norm_rpow hk').subtype (congrSet N a)
  simp only [tendstoLocallyUniformly_iff_forall_isCompact, eisensteinG_eq]
  intro K hK
  obtain ⟨A, B, hB, HABK⟩ := subset_verticalStrip_of_isCompact hK
  refine (tendstoUniformlyOn_tsum (hu := p_sum.mul_left <| r ⟨⟨A, B⟩, hB⟩ ^ (-k : ℝ))
    (fun p z hz => ?_)).mono HABK
  simpa only [eisSummand, one_div, ← zpow_neg, norm_zpow, ← Real.rpow_intCast,
    Int.cast_neg] using summand_bound_of_mem_verticalStrip (by positivity) p hB hz

lemma eisensteinG_tendstoLocallyUniformlyOn (hk : 3 ≤ k) (a : Fin 2 → ZMod N) :
    TendstoLocallyUniformlyOn (fun (s : Finset (congrSet N a)) =>
      ↑ₕ(fun (z : ℍ) => ∑ x ∈ s, eisSummand k x z)) (↑ₕ(eisensteinGSIF N k a))
          Filter.atTop {z : ℂ | 0 < z.im} := by
  rw [← upperHalfPlaneSet, ← UpperHalfPlane.range_coe, ← Set.image_univ]
  apply TendstoLocallyUniformlyOn.comp (s := ⊤) _ _ _ (OpenPartialHomeomorph.continuousOn_symm _)
  · simp only [Set.top_eq_univ, tendstoLocallyUniformlyOn_univ]
    apply eisensteinG_tendstoLocallyUniformly hk
  · simp only [Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target, Set.top_eq_univ,
      Set.mapsTo_range_iff, Set.mem_univ, forall_const]

theorem eisensteinGSIF_mdifferentiable (hk : 3 ≤ k) (a : Fin 2 → ZMod N) :
    MDiff (eisensteinGSIF N k a) := by
  intro τ
  suffices DifferentiableAt ℂ (↑ₕeisensteinGSIF N k a) τ.1 by
    convert!
      MDifferentiableAt.comp τ (DifferentiableAt.mdifferentiableAt this) τ.mdifferentiable_coe
    exact funext fun z => (comp_ofComplex (eisensteinGSIF N k a) z).symm
  refine DifferentiableOn.differentiableAt ?_ (isOpen_upperHalfPlaneSet.mem_nhds τ.2)
  exact (eisensteinG_tendstoLocallyUniformlyOn hk a).differentiableOn
    (Eventually.of_forall fun s => DifferentiableOn.fun_sum
    fun _ _ => eisSummand_extension_differentiableOn _ _) isOpen_upperHalfPlaneSet

private lemma norm_le_tsum_norm_eisensteinG (N : ℕ) (a : Fin 2 → ZMod N) (k : ℤ) (hk : 3 ≤ k) (z : ℍ) :
    ‖EisensteinSeries.eisensteinG N k a z‖ ≤ ∑' (x : Fin 2 → ℤ), ‖eisSummand k x z‖ := by
  rw [eisensteinG_eq]
  apply le_trans (norm_tsum_le_tsum_norm ((summable_norm_eisSummand hk z).subtype _))
    (Summable.tsum_subtype_le (fun (x : Fin 2 → ℤ) => ‖(eisSummand k x z)‖) _ (fun _ => norm_nonneg _)
      (summable_norm_eisSummand hk z))

theorem isBoundedAtImInfty_eisensteinGSIF_slash [NeZero N] (a : Fin 2 → ZMod N)
    (hk : 3 ≤ k) (A : SL(2, ℤ)) : IsBoundedAtImInfty (eisensteinGSIF N k a ∣[k] A) := by
  simp_rw [UpperHalfPlane.isBoundedAtImInfty_iff, coe_eisensteinGSIF] at *
  refine ⟨∑'(x : Fin 2 → ℤ), r ⟨⟨N, 2⟩, Nat.ofNat_pos⟩ ^ (-k) * ‖x‖ ^ (-k), 2, ?_⟩
  intro z hz
  obtain ⟨n, hn⟩ := (ModularGroup_T_zpow_mem_verticalStrip z (NeZero.pos N))
  rw [eisensteinG_slash_apply, ← eisensteinGSIF_apply,
    ← SlashInvariantForm.T_zpow_width_invariant N k n (eisensteinGSIF N k (a ᵥ* A)) z]
  apply le_trans (norm_le_tsum_norm_eisensteinG N (a ᵥ* A) k hk _)
  have hk' : (2 : ℝ) < k := by norm_cast
  apply (summable_norm_eisSummand hk _).tsum_le_tsum _
  · exact_mod_cast (summable_one_div_norm_rpow hk').mul_left <| r ⟨⟨N, 2⟩, Nat.ofNat_pos⟩ ^ (-k)
  · intro x
    simp_rw [eisSummand, norm_zpow]
    exact_mod_cast
      summand_bound_of_mem_verticalStrip (lt_trans two_pos hk').le x two_pos
      (verticalStrip_anti_right N hz hn)

/-- `eisensteinG` as a modular form on `Γ(N)`: the canonical witness of
`exists_modularForm_coe_eq_eisensteinG`. -/
noncomputable def eisensteinGMF [NeZero N] (hk : 3 ≤ k) (a : Fin 2 → ZMod N) : ModularForm Γ(N) k where
  toFun := eisensteinGSIF N k a
  slash_action_eq' := (eisensteinGSIF N k a).slash_action_eq'
  holo' := eisensteinGSIF_mdifferentiable hk a
  bdd_at_cusps' {c} hc := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    exact fun γ hγ => isBoundedAtImInfty_eisensteinGSIF_slash a hk γ

/-- The `ModularForm` bundle of `eisensteinG`, and its coercion back to the series. -/
lemma coe_eisensteinGMF [NeZero N] (hk : 3 ≤ k) (a : Fin 2 → ZMod N) :
    ⇑(eisensteinGMF hk a) = EisensteinSeries.eisensteinG N k a := rfl

theorem exists_modularForm_coe_eq_eisensteinG (N : ℕ) [NeZero N] (k : ℤ) (hk : 3 ≤ k) (a : Fin 2 → ZMod N) :
    (∃ F : ModularForm Γ(N) k, ⇑F = EisensteinSeries.eisensteinG N k a) ∧
      ∀ γ : SL(2, ℤ), EisensteinSeries.eisensteinG N k a ∣[k] γ =
        EisensteinSeries.eisensteinG N k (a ᵥ* γ) :=
  ⟨⟨eisensteinGMF hk a, rfl⟩, eisensteinG_slash_apply N k a⟩

/-! ### Boundedness at `∞`, periodicity, and the `q`-expansion -/

theorem isBoundedAtImInfty_eisensteinG [NeZero N] (a : Fin 2 → ZMod N) (hk : 3 ≤ k) :
    IsBoundedAtImInfty (EisensteinSeries.eisensteinG N k a) := by
  simp_rw [UpperHalfPlane.isBoundedAtImInfty_iff]
  refine ⟨∑'(x : Fin 2 → ℤ), r ⟨⟨N, 2⟩, Nat.ofNat_pos⟩ ^ (-k) * ‖x‖ ^ (-k), 2, ?_⟩
  intro z hz
  obtain ⟨n, hn⟩ := (ModularGroup_T_zpow_mem_verticalStrip z (NeZero.pos N))
  rw [← coe_eisensteinGSIF, ← SlashInvariantForm.T_zpow_width_invariant N k n (eisensteinGSIF N k a) z,
    coe_eisensteinGSIF]
  apply le_trans (norm_le_tsum_norm_eisensteinG N a k hk _)
  have hk' : (2 : ℝ) < k := by norm_cast
  apply (summable_norm_eisSummand hk _).tsum_le_tsum _
  · exact_mod_cast (summable_one_div_norm_rpow hk').mul_left <| r ⟨⟨N, 2⟩, Nat.ofNat_pos⟩ ^ (-k)
  · intro x
    simp_rw [eisSummand, norm_zpow]
    exact_mod_cast
      summand_bound_of_mem_verticalStrip (lt_trans two_pos hk').le x two_pos
      (verticalStrip_anti_right N hz hn)

lemma periodic_eisensteinG (k : ℤ) (a : Fin 2 → ZMod N) :
    Function.Periodic (EisensteinSeries.eisensteinG N k a ∘ ofComplex) (N : ℝ) := by
  have hT : EisensteinSeries.eisensteinG N k a ∣[k] (ModularGroup.T ^ (N : ℤ)) =
      EisensteinSeries.eisensteinG N k a := by
    have hmem : ModularGroup.T ^ (N : ℤ) ∈ Γ(N) := by
      simpa using CongruenceSubgroup.ModularGroup_T_pow_mem_Gamma (N : ℤ) (N : ℤ) dvd_rfl
    have := SlashInvariantForm.slash_action_eqn (eisensteinGSIF N k a)
      (Matrix.SpecialLinearGroup.mapGL ℝ (ModularGroup.T ^ (N : ℤ))) ⟨_, hmem, rfl⟩
    simp [ModularForm.SL_slash, Matrix.SpecialLinearGroup.mapGL] at this ⊢
    exact this
  intro w
  by_cases hw : 0 < w.im
  · have hw' : 0 < (w + ((N : ℝ) : ℂ)).im := by simpa using hw
    simp only [Function.comp_apply]
    rw [ofComplex_apply_of_im_pos hw', ofComplex_apply_of_im_pos hw]
    have h1 : (⟨w + ((N : ℝ) : ℂ), hw'⟩ : ℍ) = (((N : ℤ) : ℝ)) +ᵥ (⟨w, hw⟩ : ℍ) := by
      apply UpperHalfPlane.ext; simp [UpperHalfPlane.coe_vadd, add_comm]
    rw [h1, ← slash_T_zpow_apply (EisensteinSeries.eisensteinG N k a) (N : ℤ), hT]
  · have hw' : (w + ((N : ℝ) : ℂ)).im ≤ 0 := by simpa using hw
    simp only [Function.comp_apply]
    rw [ofComplex_apply_of_im_nonpos hw', ofComplex_apply_of_im_nonpos (not_lt.mp hw)]

private theorem qExpansion_coeff_eq [NeZero N] (hk : 3 ≤ k) (a : Fin 2 → ZMod N) {c : ℕ → ℂ}
    (hsum : ∀ τ : ℍ, HasSum (fun m => c m * Function.Periodic.qParam N τ ^ m)
      (EisensteinSeries.eisensteinG N k a τ)) (n : ℕ) :
    (qExpansion N (EisensteinSeries.eisensteinG N k a)).coeff n = c n := by
  have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hA : AnalyticAt ℂ (cuspFunction N ⇑(eisensteinGSIF N k a)) 0 :=
    analyticAt_cuspFunction_zero hN (periodic_eisensteinG k a) (eisensteinGSIF_mdifferentiable hk a)
      (isBoundedAtImInfty_eisensteinG a hk)
  have := qExpansion_coeff_unique (eisensteinGSIF N k a) hN hA (c := c)
    (fun τ => by have h__af := hsum τ; simp [smul_eq_mul] at h__af ⊢; exact h__af) n
  rw [coe_eisensteinGSIF] at this
  exact this.symm

section expansion

variable [NeZero N] {k : ℕ}

/-! ### The double-sum form and the divisor-sum coefficients -/

/-- `congrSet N a` as the product of its two one-dimensional residue classes. -/
def congrSetEquivSigma (a : Fin 2 → ZMod N) : congrSet N a ≃ (Σ _ : cls N (a 0), cls N (a 1)) where
  toFun v := ⟨⟨v.1 0, congr_fun v.2 0⟩, ⟨v.1 1, congr_fun v.2 1⟩⟩
  invFun p := ⟨![p.1.1, p.2.1], by
    show ((↑) : ℤ → ZMod N) ∘ ![p.1.1, p.2.1] = a
    funext i; fin_cases i
    · simpa using p.1.2
    · simpa using p.2.2⟩
  left_inv v := by
    apply Subtype.ext
    funext i; fin_cases i <;> rfl
  right_inv p := by
    rcases p with ⟨⟨c, hc⟩, ⟨d, hd⟩⟩
    rfl

omit [NeZero N] in
lemma eisSummand_natCast (v : Fin 2 → ℤ) (z : ℍ) :
    eisSummand (k : ℤ) v z = ((((v 0 : ℂ)) * z + v 1) ^ k)⁻¹ := by
  rw [eisSummand, zpow_neg, zpow_natCast]

omit [NeZero N] in

lemma eisensteinG_eq_tsum_tsum (hk : 3 ≤ k) (a : Fin 2 → ZMod N) (τ : ℍ) :
    EisensteinSeries.eisensteinG N k a τ =
      ∑' c : cls N (a 0), ∑' d : cls N (a 1), ((((c.1 : ℂ)) * τ + d.1) ^ k)⁻¹ := by
  have hk' : 3 ≤ ((k : ℕ) : ℤ) := by exact_mod_cast hk
  rw [eisensteinG_eq]
  dsimp only
  rw [← (congrSetEquivSigma a).symm.tsum_eq]
  have hs : Summable (fun p : Σ _ : cls N (a 0), cls N (a 1) =>
      eisSummand (k : ℤ) ((congrSetEquivSigma a).symm p).1 τ) :=
    (congrSetEquivSigma a).symm.summable_iff.mpr ((summable_norm_eisSummand hk' τ).of_norm.subtype _)
  rw [hs.tsum_sigma]
  refine tsum_congr fun c => tsum_congr fun d => ?_
  rw [eisSummand_natCast]
  rfl

private def wpt (c : ℕ) (hc : 0 < c) (bv : ℕ) (τ : ℍ) : ℍ :=
  ⟨(((c : ℂ)) * τ + bv) / N, by
    have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
    rw [Complex.div_natCast_im]
    apply div_pos _ hN
    simp only [Complex.add_im, Complex.mul_im, Complex.natCast_re, Complex.natCast_im, zero_mul,
      add_zero, UpperHalfPlane.coe_im, UpperHalfPlane.coe_re]
    exact mul_pos (Nat.cast_pos.mpr hc) τ.2⟩

private lemma stdAddChar_mul_natCast (b : ZMod N) (bv : ℕ) (hbv : (bv : ZMod N) = b) (m : ℕ) :
    ZMod.stdAddChar (b * (m : ZMod N)) = cexp (2 * π * I * (((bv * m : ℕ) : ℤ) : ℂ) / N) := by
  have : (b * (m : ZMod N) : ZMod N) = (((bv * m : ℕ) : ℤ) : ZMod N) := by
    rw [← hbv]; push_cast; ring
  rw [this, ZMod.stdAddChar_coe]

private lemma tsum_int_eq (hk : 2 ≤ k) (b : ZMod N) (bv : ℕ) (hbv : (bv : ZMod N) = b) (c : ℕ) (hc : 0 < c)
    (τ : ℍ) :
    ∑' j : ℤ, ((((c : ℂ)) * τ + ((bv : ℂ) + (N : ℂ) * j)) ^ k)⁻¹ =
      ((N : ℂ) ^ k)⁻¹ * ((-2 * π * I) ^ k / (k - 1)!) *
        ∑' m : ℕ+, ((m : ℕ) : ℂ) ^ (k - 1) *
          (ZMod.stdAddChar (b * ((m : ℕ) : ZMod N)) * Function.Periodic.qParam N τ ^ ((m : ℕ) * c)) := by
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N

  have hfac : ∀ j : ℤ, ((((c : ℂ)) * τ + ((bv : ℂ) + (N : ℂ) * j)) ^ k)⁻¹ =
      ((N : ℂ) ^ k)⁻¹ * (1 / (((wpt (N := N) c hc bv τ : ℍ) : ℂ) + j) ^ k) := by
    intro j
    rw [one_div, ← mul_inv, ← mul_pow]
    congr 2
    simp only [wpt, UpperHalfPlane.coe_mk]
    field_simp
    ring
  simp_rw [hfac]
  rw [tsum_mul_left, mul_assoc]
  congr 1

  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hk1 : 1 ≤ k' := by omega
  rw [EisensteinSeries.qExpansion_identity_pnat hk1 (wpt (N := N) c hc bv τ)]
  simp only [Nat.add_sub_cancel]
  congr 1
  refine tsum_congr fun m => ?_
  congr 1
  rw [stdAddChar_mul_natCast b bv hbv, Function.Periodic.qParam, ← Complex.exp_nat_mul,
    ← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  simp only [wpt, UpperHalfPlane.coe_mk]
  push_cast
  field_simp
  ring

private lemma tsum_cls_eq (hk : 2 ≤ k) (b : ZMod N) (c : ℕ) (hc : 0 < c) (τ : ℍ) :
    ∑' d : cls N b, ((((c : ℂ)) * τ + d.1) ^ k)⁻¹ =
      ((N : ℂ) ^ k)⁻¹ * ((-2 * π * I) ^ k / (k - 1)!) *
        ∑' m : ℕ+, ((m : ℕ) : ℂ) ^ (k - 1) *
          (ZMod.stdAddChar (b * ((m : ℕ) : ZMod N)) * Function.Periodic.qParam N τ ^ ((m : ℕ) * c)) := by
  rw [← (clsEquiv b).tsum_eq]
  have : ∀ j : ℤ, ((((c : ℂ)) * τ + ((clsEquiv b j).1 : ℂ)) ^ k)⁻¹ =
      ((((c : ℂ)) * τ + (((b.val : ℕ) : ℂ) + (N : ℂ) * j)) ^ k)⁻¹ := by
    intro j
    simp only [clsEquiv, Equiv.coe_fn_mk, Int.cast_add, Int.cast_mul, Int.cast_natCast]
  simp_rw [this]
  exact tsum_int_eq hk b b.val (ZMod.natCast_zmod_val b) c hc τ

omit [NeZero N] in

private lemma tsum_cls_neg_eq (b : ZMod N) (c : ℕ) (τ : ℍ) :
    ∑' d : cls N b, (((((-(c : ℤ) : ℤ) : ℂ)) * τ + d.1) ^ k)⁻¹ =
      (-1) ^ k * ∑' d : cls N (-b), ((((c : ℂ)) * τ + d.1) ^ k)⁻¹ := by
  rw [← (clsNegEquiv b).symm.tsum_eq, ← tsum_mul_left]
  refine tsum_congr fun d => ?_
  simp only [clsNegEquiv, Equiv.coe_fn_symm_mk, Int.cast_neg, Int.cast_natCast]
  rw [show (-(c : ℂ)) * τ + -((d.1 : ℤ) : ℂ) = (-1) * ((c : ℂ) * τ + d.1) by ring, mul_pow, mul_inv,
    ← inv_pow, inv_neg, inv_one]

omit [NeZero N] in

private lemma summable_inner (hk : 3 ≤ k) (b : ZMod N) (τ : ℍ) :
    Summable fun c : ℤ => ∑' d : cls N b, ((((c : ℂ)) * τ + d.1) ^ k)⁻¹ := by
  have hk' : 3 ≤ ((k : ℕ) : ℤ) := by exact_mod_cast hk

  have hfull : Summable fun p : ℤ × ℤ => ‖eisSummand (k : ℤ) ![p.1, p.2] τ‖ := by
    have := (summable_norm_eisSummand hk' τ)
    rw [← (finTwoArrowEquiv ℤ).symm.summable_iff] at this
    refine this.congr fun p => ?_
    simp only [Function.comp_apply, finTwoArrowEquiv_symm_apply]
  refine Summable.of_norm_bounded hfull.prod fun c => ?_
  have hsub : Summable fun d : cls N b => ‖((((c : ℂ)) * τ + d.1) ^ k)⁻¹‖ := by
    have := (hfull.prod_factor c)
    refine (this.subtype {d : ℤ | (d : ZMod N) = b}).congr fun d => ?_
    simp [eisSummand_natCast]
  refine (norm_tsum_le_tsum_norm hsub).trans ?_
  have := Summable.tsum_subtype_le (fun d : ℤ => ‖((((c : ℂ)) * τ + d) ^ k)⁻¹‖) {d : ℤ | (d : ZMod N) = b}
    (fun _ => norm_nonneg _) ((hfull.prod_factor c).congr fun d => by simp [eisSummand_natCast])
  refine this.trans (le_of_eq (tsum_congr fun d => ?_))
  simp [eisSummand_natCast]

private def kappa (N k : ℕ) : ℂ := ((N : ℂ) ^ k)⁻¹ * ((-2 * π * I) ^ k / (k - 1)!)

private def Splus (N k : ℕ) [NeZero N] (a : Fin 2 → ZMod N) (n : ℕ+) : ℂ :=
  ∑ x ∈ (n : ℕ).divisorsAntidiagonal,
    (if ((x.1 : ℕ) : ZMod N) = a 0 then (1 : ℂ) else 0) * ZMod.stdAddChar (a 1 * ((x.2 : ℕ) : ZMod N)) *
      ((x.2 : ℕ) : ℂ) ^ (k - 1)

private def Sminus (N k : ℕ) [NeZero N] (a : Fin 2 → ZMod N) (n : ℕ+) : ℂ :=
  ∑ x ∈ (n : ℕ).divisorsAntidiagonal,
    (if ((x.1 : ℕ) : ZMod N) = -a 0 then (1 : ℂ) else 0) * ZMod.stdAddChar (-a 1 * ((x.2 : ℕ) : ZMod N)) *
      ((x.2 : ℕ) : ℂ) ^ (k - 1)

private def coefFun (N k : ℕ) [NeZero N] (a : Fin 2 → ZMod N) (n : ℕ) : ℂ :=
  if h : n = 0 then (if a 0 = 0 then ∑' d : cls N (a 1), (((d.1 : ℂ)) ^ k)⁻¹ else 0)
  else kappa N k * (Splus N k a ⟨n, Nat.pos_of_ne_zero h⟩ + (-1) ^ k * Sminus N k a ⟨n, Nat.pos_of_ne_zero h⟩)

lemma norm_stdAddChar (x : ZMod N) : ‖ZMod.stdAddChar x‖ = 1 := by
  rw [ZMod.stdAddChar_apply]; exact Circle.norm_coe _

private lemma norm_divisorSum_le (hk : 1 ≤ k) (b b' : ZMod N) (n : ℕ+) :
    ‖∑ x ∈ (n : ℕ).divisorsAntidiagonal,
      (if ((x.1 : ℕ) : ZMod N) = b then (1 : ℂ) else 0) * ZMod.stdAddChar (b' * ((x.2 : ℕ) : ZMod N)) *
        ((x.2 : ℕ) : ℂ) ^ (k - 1)‖ ≤ ((n : ℕ) : ℝ) ^ k := by
  refine (norm_sum_le _ _).trans ?_
  have hle : ∀ x ∈ (n : ℕ).divisorsAntidiagonal,
      ‖(if ((x.1 : ℕ) : ZMod N) = b then (1 : ℂ) else 0) * ZMod.stdAddChar (b' * ((x.2 : ℕ) : ZMod N)) *
        ((x.2 : ℕ) : ℂ) ^ (k - 1)‖ ≤ (fun i j : ℕ => ((j : ℝ)) ^ (k - 1)) x.1 x.2 := by
    intro x hx
    rw [norm_mul, norm_mul, norm_stdAddChar, mul_one, norm_pow, Complex.norm_natCast]
    calc ‖(if ((x.1 : ℕ) : ZMod N) = b then (1 : ℂ) else 0)‖ * (x.2 : ℝ) ^ (k - 1)
        ≤ 1 * (x.2 : ℝ) ^ (k - 1) := by
          gcongr; split_ifs <;> simp
      _ = (x.2 : ℝ) ^ (k - 1) := one_mul _
  refine (Finset.sum_le_sum hle).trans ?_
  rw [Nat.sum_divisorsAntidiagonal (fun i j : ℕ => ((j : ℝ)) ^ (k - 1))]
  have hle2 : ∀ i ∈ (n : ℕ).divisors, (((n : ℕ) / i : ℕ) : ℝ) ^ (k - 1) ≤ ((n : ℕ) : ℝ) ^ (k - 1) := by
    intro i hi
    gcongr
    exact_mod_cast Nat.div_le_self _ _
  refine (Finset.sum_le_card_nsmul _ _ _ hle2).trans ?_
  rw [nsmul_eq_mul]
  calc ((((n : ℕ).divisors.card : ℕ) : ℝ)) * ((n : ℕ) : ℝ) ^ (k - 1)
      ≤ ((n : ℕ) : ℝ) * ((n : ℕ) : ℝ) ^ (k - 1) := by
        gcongr; exact_mod_cast Nat.card_divisors_le_self _
    _ = ((n : ℕ) : ℝ) ^ k := by rw [← pow_succ']; congr 1; omega

private lemma summable_divisorSum_mul_pow (hk : 1 ≤ k) (b b' : ZMod N) {r : ℂ} (hr : ‖r‖ < 1) :
    Summable fun n : ℕ+ => (∑ x ∈ (n : ℕ).divisorsAntidiagonal,
      (if ((x.1 : ℕ) : ZMod N) = b then (1 : ℂ) else 0) * ZMod.stdAddChar (b' * ((x.2 : ℕ) : ZMod N)) *
        ((x.2 : ℕ) : ℂ) ^ (k - 1)) * r ^ (n : ℕ) := by
  have hs : Summable fun n : ℕ => ‖((n : ℂ)) ^ k * r ^ n‖ := summable_norm_pow_mul_geometric_of_norm_lt_one k hr
  refine Summable.of_norm_bounded (hs.subtype _) fun n => ?_
  simp only [norm_mul, norm_pow, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_right (norm_divisorSum_le hk b b' n) (by positivity)

private theorem eisensteinG_eq_expansion (hk : 3 ≤ k) (a : Fin 2 → ZMod N) (τ : ℍ) :
    EisensteinSeries.eisensteinG N k a τ =
      (if a 0 = 0 then ∑' d : cls N (a 1), (((d.1 : ℂ)) ^ k)⁻¹ else 0) +
        ∑' n : ℕ+, kappa N k * (Splus N k a n + (-1) ^ k * Sminus N k a n) *
          Function.Periodic.qParam N τ ^ (n : ℕ) := by
  set q := Function.Periodic.qParam N τ with hq
  have hqn : ‖q‖ < 1 := UpperHalfPlane.norm_qParam_lt_one N τ

  rw [eisensteinG_eq_tsum_tsum hk a τ,
    tsum_cls_split (a 0) (fun c : ℤ => ∑' d : cls N (a 1), ((((c : ℂ)) * τ + d.1) ^ k)⁻¹)
      (summable_inner hk (a 1) τ)]
  have hpos : ∀ c : ℕ+, (∑' d : cls N (a 1), (((((c : ℕ) : ℤ) : ℂ) * τ + d.1) ^ k)⁻¹) =
      kappa N k * ∑' m : ℕ+, ((m : ℕ) : ℂ) ^ (k - 1) *
        (ZMod.stdAddChar (a 1 * ((m : ℕ) : ZMod N)) * q ^ ((m : ℕ) * (c : ℕ))) := by
    intro c
    have := tsum_cls_eq (show 2 ≤ k by omega) (a 1) (c : ℕ) c.2 τ
    simpa [kappa] using this
  have hneg : ∀ c : ℕ+, (∑' d : cls N (a 1), ((((-((c : ℕ) : ℤ) : ℤ) : ℂ) * τ + d.1) ^ k)⁻¹) =
      (-1) ^ k * (kappa N k * ∑' m : ℕ+, ((m : ℕ) : ℂ) ^ (k - 1) *
        (ZMod.stdAddChar (-a 1 * ((m : ℕ) : ZMod N)) * q ^ ((m : ℕ) * (c : ℕ)))) := by
    intro c
    rw [tsum_cls_neg_eq (a 1) (c : ℕ) τ, tsum_cls_eq (show 2 ≤ k by omega) (-a 1) (c : ℕ) c.2 τ, kappa]
  simp only [Int.cast_zero, zero_mul, zero_add]

  have e0 : (if (0 : ZMod N) = a 0 then ∑' d : cls N (a 1), (((d.1 : ℂ)) ^ k)⁻¹ else 0) =
      (if a 0 = 0 then ∑' d : cls N (a 1), (((d.1 : ℂ)) ^ k)⁻¹ else 0) := by
    simp only [eq_comm]
  have epos : (∑' c : ℕ+, if (((c : ℕ)) : ZMod N) = a 0 then
      ∑' d : cls N (a 1), (((((c : ℕ) : ℤ) : ℂ) * τ + d.1) ^ k)⁻¹ else 0) =
      kappa N k * ∑' n : ℕ+, Splus N k a n * q ^ (n : ℕ) := by
    have h1 : ∀ c : ℕ+, (if (((c : ℕ)) : ZMod N) = a 0 then
        ∑' d : cls N (a 1), (((((c : ℕ) : ℤ) : ℂ) * τ + d.1) ^ k)⁻¹ else 0) =
        kappa N k * ((if (((c : ℕ) : ℕ) : ZMod N) = a 0 then (1 : ℂ) else 0) *
          ∑' m : ℕ+, ((m : ℕ) : ℂ) ^ (k - 1) *
            (ZMod.stdAddChar (a 1 * ((m : ℕ) : ZMod N)) * q ^ ((m : ℕ) * (c : ℕ)))) := by
      intro c
      rw [hpos c]
      split_ifs <;> simp
    simp_rw [h1]
    rw [tsum_mul_left]
    congr 1
    exact tsum_tsum_eq_tsum_antidiagonal (F := fun c : ℕ => if ((c : ℕ) : ZMod N) = a 0 then (1 : ℂ) else 0)
      (G := fun m : ℕ => ZMod.stdAddChar (a 1 * ((m : ℕ) : ZMod N)))
      (fun c => by split_ifs <;> simp) (fun m => (norm_stdAddChar _).le) hqn (k - 1)
  have eneg : (∑' c : ℕ+, if ((-((c : ℕ) : ℤ) : ℤ) : ZMod N) = a 0 then
      ∑' d : cls N (a 1), ((((-((c : ℕ) : ℤ) : ℤ) : ℂ) * τ + d.1) ^ k)⁻¹ else 0) =
      (-1) ^ k * (kappa N k * ∑' n : ℕ+, Sminus N k a n * q ^ (n : ℕ)) := by
    have h1 : ∀ c : ℕ+, (if ((-((c : ℕ) : ℤ) : ℤ) : ZMod N) = a 0 then
        ∑' d : cls N (a 1), ((((-((c : ℕ) : ℤ) : ℤ) : ℂ) * τ + d.1) ^ k)⁻¹ else 0) =
        (-1) ^ k * (kappa N k * ((if (((c : ℕ) : ℕ) : ZMod N) = -a 0 then (1 : ℂ) else 0) *
          ∑' m : ℕ+, ((m : ℕ) : ℂ) ^ (k - 1) *
            (ZMod.stdAddChar (-a 1 * ((m : ℕ) : ZMod N)) * q ^ ((m : ℕ) * (c : ℕ))))) := by
      intro c
      rw [hneg c]
      have hiff : ((-((c : ℕ) : ℤ) : ℤ) : ZMod N) = a 0 ↔ (((c : ℕ) : ℕ) : ZMod N) = -a 0 := by
        rw [Int.cast_neg, Int.cast_natCast, neg_eq_iff_eq_neg]
      simp only [hiff]
      split_ifs <;> simp
    simp_rw [h1]
    rw [tsum_mul_left, tsum_mul_left]
    congr 2
    exact tsum_tsum_eq_tsum_antidiagonal (F := fun c : ℕ => if ((c : ℕ) : ZMod N) = -a 0 then (1 : ℂ) else 0)
      (G := fun m : ℕ => ZMod.stdAddChar (-a 1 * ((m : ℕ) : ZMod N)))
      (fun c => by split_ifs <;> simp) (fun m => (norm_stdAddChar _).le) hqn (k - 1)
  rw [e0, epos, eneg, add_assoc]
  congr 1

  have hs1 : Summable fun n : ℕ+ => kappa N k * (Splus N k a n * q ^ (n : ℕ)) :=
    (summable_divisorSum_mul_pow (show 1 ≤ k by omega) (a 0) (a 1) hqn).mul_left _
  have hs2 : Summable fun n : ℕ+ => (-1) ^ k * (kappa N k * (Sminus N k a n * q ^ (n : ℕ))) :=
    ((summable_divisorSum_mul_pow (show 1 ≤ k by omega) (-a 0) (-a 1) hqn).mul_left _).mul_left _
  change kappa N k * ∑' n : ℕ+, Splus N k a n * q ^ (n : ℕ) +
    (-1) ^ k * (kappa N k * ∑' n : ℕ+, Sminus N k a n * q ^ (n : ℕ)) = _
  rw [← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left, ← hs1.tsum_add hs2]
  refine tsum_congr fun n => ?_
  ring

private theorem hasSum_coefFun (hk : 3 ≤ k) (a : Fin 2 → ZMod N) (τ : ℍ) :
    HasSum (fun n : ℕ => coefFun N k a n * Function.Periodic.qParam N τ ^ n)
      (EisensteinSeries.eisensteinG N k a τ) := by
  set q := Function.Periodic.qParam N τ with hq
  have hqn : ‖q‖ < 1 := UpperHalfPlane.norm_qParam_lt_one N τ
  have hs1 := summable_divisorSum_mul_pow (show 1 ≤ k by omega) (a 0) (a 1) hqn
  have hs2 := summable_divisorSum_mul_pow (show 1 ≤ k by omega) (-a 0) (-a 1) hqn
  have hpn : ∀ n : ℕ+, coefFun N k a n * q ^ (n : ℕ) =
      kappa N k * (Splus N k a n + (-1) ^ k * Sminus N k a n) * q ^ (n : ℕ) := by
    intro n
    simp only [coefFun, PNat.ne_zero, ↓reduceDIte]
    rfl
  have hsum : Summable fun n : ℕ+ => coefFun N k a n * q ^ (n : ℕ) := by
    simp_rw [hpn]
    have := ((hs1.add (hs2.mul_left ((-1 : ℂ) ^ k))).mul_left (kappa N k))
    refine this.congr fun n => ?_
    simp only [Splus, Sminus]
    ring
  have hsumN : Summable fun n : ℕ => coefFun N k a n * q ^ n := summable_pnat_iff_summable_nat.mp hsum
  have htsum : ∑' n : ℕ, coefFun N k a n * q ^ n = EisensteinSeries.eisensteinG N k a τ := by
    rw [← tsum_zero_pnat_eq_tsum_nat hsumN, eisensteinG_eq_expansion hk a τ]
    simp_rw [hpn]
    congr 1
    simp [coefFun]
  exact htsum ▸ hsumN.hasSum

private theorem qExpansion_coeff_formula (hk : 3 ≤ k) (a : Fin 2 → ZMod N) (n : ℕ) :
    (qExpansion N (EisensteinSeries.eisensteinG N k a)).coeff n =
      if n = 0 then
        (if a 0 = 0 then ∑' d : {d : ℤ // (d : ZMod N) = a 1}, ((d : ℂ) ^ k)⁻¹ else 0)
      else
        (-2 * π * I) ^ k / ((k - 1)! * (N : ℂ) ^ k) *
          ∑ m ∈ n.divisors,
            ((if ((n / m : ℕ) : ZMod N) = a 0 then ZMod.stdAddChar (a 1 * (m : ZMod N)) else 0) +
              (-1) ^ k *
                (if ((n / m : ℕ) : ZMod N) = -a 0 then ZMod.stdAddChar (-(a 1 * (m : ZMod N))) else 0)) *
            (m : ℂ) ^ (k - 1) := by
  have hk' : 3 ≤ ((k : ℕ) : ℤ) := by exact_mod_cast hk
  rw [qExpansion_coeff_eq hk' a (hasSum_coefFun hk a) n, coefFun]
  by_cases hn : n = 0
  · subst hn
    rfl
  ·
    rw [dite_eq_right hn, ite_eq_right hn]
    have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
    simp only [kappa, Splus, Sminus]
    rw [Nat.sum_divisorsAntidiagonal' (fun i j : ℕ =>
        (if ((i : ℕ) : ZMod N) = a 0 then (1 : ℂ) else 0) * ZMod.stdAddChar (a 1 * ((j : ℕ) : ZMod N)) *
          ((j : ℕ) : ℂ) ^ (k - 1)),
      Nat.sum_divisorsAntidiagonal' (fun i j : ℕ =>
        (if ((i : ℕ) : ZMod N) = -a 0 then (1 : ℂ) else 0) * ZMod.stdAddChar (-a 1 * ((j : ℕ) : ZMod N)) *
          ((j : ℕ) : ℂ) ^ (k - 1))]
    simp only [PNat.mk_coe]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [neg_mul]
    by_cases h1 : (((n / m : ℕ)) : ZMod N) = a 0
    · by_cases h2 : (((n / m : ℕ)) : ZMod N) = -a 0
      · simp_all only [↓reduceIte]; field_simp; ring_nf
      · simp_all only [↓reduceIte]; field_simp; ring_nf
    · by_cases h2 : (((n / m : ℕ)) : ZMod N) = -a 0
      · simp_all only [↓reduceIte]; field_simp; ring_nf
      · simp_all only [↓reduceIte]; field_simp; ring_nf

end expansion

theorem qExpansion_eisensteinG_coeff (N : ℕ) [NeZero N] (k : ℕ) (hk : 3 ≤ k)
    (a : Fin 2 → ZMod N) (n : ℕ) :
    (UpperHalfPlane.qExpansion N (EisensteinSeries.eisensteinG N k a)).coeff n =
      if n = 0 then
        (if a 0 = 0 then ∑' d : {d : ℤ // (d : ZMod N) = a 1}, ((d : ℂ) ^ k)⁻¹ else 0)
      else
        (-2 * π * I) ^ k / ((k - 1)! * (N : ℂ) ^ k) *
          ∑ m ∈ n.divisors,
            ((if ((n / m : ℕ) : ZMod N) = a 0 then ZMod.stdAddChar (a 1 * (m : ZMod N)) else 0) +
              (-1) ^ k *
                (if ((n / m : ℕ) : ZMod N) = -a 0 then ZMod.stdAddChar (-(a 1 * (m : ZMod N))) else 0)) *
            (m : ℂ) ^ (k - 1) :=
  qExpansion_coeff_formula hk a n

end EisensteinSeries

end
