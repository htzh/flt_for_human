/-
  The level-`N` function field of `X(N)`: the shared prelude.

  This is the one home for the blocks the eight headline files of
  `topics/modularCurve/WORKORDER-A-levelN-field.md` repeat.  The pin's `S_` files
  declare these blocks publicly, so they are written once, publicly, here at the
  pin's names and statements; the headline modules import them instead of
  re-deriving their own copies (the work order's section 3, `port_advise` block 1 of
  `tools/deps/build/mc_a_advise.txt`).

  Contents, in the pin's own section order:

  * `Toolkit` — the `Good` predicate for `Γ`-periodic, differentiable, bounded
    functions on `ℍ`, its closure laws, and the `q`-expansion series `Q` with
    `Q_eq_zero_iff` (`S_..._algHom...:29-136` = `S_..._ord_neg...:29-133` =
    `S_..._valuation...:26-133`);
  * `LevelOne` — `Δ` boundedness/non-vanishing and `Q N Δ ≠ 0`
    (`S_..._algHom...:138-190` = `S_..._valuation...:135-187`);
  * `Ring` — membership in `ring N` gives differentiability and no zero
    divisors, the slash action of `Γ(N)`, `T ^ N`, and `N`-periodicity
    (`S_..._algHom...:192-307`, identical in all six files that carry it);
  * `Expansion` — `castN_pos`, the predicate `PB F m` (bounded `F * Δ ^ m`),
    its shift law and `good_of_PB` (`S_..._valuation...:306-330`);
  * `Width` — `qParam_pow_mul` and `Q_natCast_eq_qExpand`
    (`S_..._valuation...:332-410`, identical in `S_..._algHom...:465-575`).

  The pin's `p2m_export`/`p2m_open` scaffolding, its `set_option
  linter.unusedSectionVars false` / `linter.unusedVariables false` lines (the
  project's linter set does not contain those classes) and its local
  `set_option maxHeartbeats 1600000 in` (below the project's `4_000_000` cap) are
  not transcribed.  Everything else — binders, names, statements — is the pin's.

  FLT provenance, pinned `aa2d8b3`:
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_LevelN_exists_algHom_laurentSeries_qExpansion.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_LevelN_exists_place_ord_neg_forall_smul_eq.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_LevelN_valuation_apply_smul_le_one_of_tendsto_div_smul.lean
-/
import FLTForHuman.ModularCurve.LevelN.FunctionField
import FLTForHuman.ModularForms.WeightOne.LevelN
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.Periodic
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.RingTheory.HahnSeries.PowerSeries
import Mathlib.RingTheory.PowerSeries.Order

set_option autoImplicit false

noncomputable section

open UpperHalfPlane Filter Topology Function

open scoped MatrixGroups Manifold Real

namespace ModularCurve

namespace LevelN

section Toolkit

variable {h : ℝ}

structure Good (h : ℝ) (G : ℍ → ℂ) : Prop where
  periodic : Periodic (G ∘ ofComplex) h
  mdiff : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G
  bdd : IsBoundedAtImInfty G

namespace Good

variable {G G₁ G₂ : ℍ → ℂ}

theorem analyticAt (hG : Good h G) (hh : 0 < h) : AnalyticAt ℂ (cuspFunction h G) 0 :=
  analyticAt_cuspFunction_zero hh hG.periodic hG.mdiff hG.bdd

theorem continuousAt (hG : Good h G) (hh : 0 < h) : ContinuousAt (cuspFunction h G) 0 :=
  (hG.analyticAt hh).continuousAt

theorem mul (h₁ : Good h G₁) (h₂ : Good h G₂) : Good h (G₁ * G₂) where
  periodic := by
    have : (G₁ * G₂) ∘ ofComplex = (G₁ ∘ ofComplex) * (G₂ ∘ ofComplex) := rfl
    rw [this]
    exact h₁.periodic.mul h₂.periodic
  mdiff := h₁.mdiff.mul h₂.mdiff
  bdd := h₁.bdd.mul h₂.bdd

theorem add (h₁ : Good h G₁) (h₂ : Good h G₂) : Good h (G₁ + G₂) where
  periodic := by
    have : (G₁ + G₂) ∘ ofComplex = (G₁ ∘ ofComplex) + (G₂ ∘ ofComplex) := rfl
    rw [this]
    exact h₁.periodic.add h₂.periodic
  mdiff := h₁.mdiff.add h₂.mdiff
  bdd := h₁.bdd.add h₂.bdd

theorem const (h : ℝ) (c : ℂ) : Good h (fun _ : ℍ => c) where
  periodic := fun _ => rfl
  mdiff := mdifferentiable_const
  bdd := Filter.const_boundedAtFilter _ _

theorem one (h : ℝ) : Good h (1 : ℍ → ℂ) := const h 1

theorem pow (hG : Good h G) : ∀ n : ℕ, Good h (G ^ n)
  | 0 => by rw [pow_zero]; exact one h
  | n + 1 => by rw [pow_succ]; exact (pow hG n).mul hG

end Good

variable {G G₁ G₂ : ℍ → ℂ}

theorem cuspFunction_mul_of_good (hh : 0 < h) (h₁ : Good h G₁) (h₂ : Good h G₂) :
    cuspFunction h (G₁ * G₂) = cuspFunction h G₁ * cuspFunction h G₂ :=
  cuspFunction_mul (h₁.continuousAt hh) (h₂.continuousAt hh)

theorem cuspFunction_add_of_good (hh : 0 < h) (h₁ : Good h G₁) (h₂ : Good h G₂) :
    cuspFunction h (G₁ + G₂) = cuspFunction h G₁ + cuspFunction h G₂ :=
  cuspFunction_add (h₁.continuousAt hh) (h₂.continuousAt hh)

theorem qExpansion_mul_of_good (hh : 0 < h) (h₁ : Good h G₁) (h₂ : Good h G₂) :
    qExpansion h (G₁ * G₂) = qExpansion h G₁ * qExpansion h G₂ :=
  qExpansion_mul (h₁.analyticAt hh) (h₂.analyticAt hh)

theorem qExpansion_add_of_good (hh : 0 < h) (h₁ : Good h G₁) (h₂ : Good h G₂) :
    qExpansion h (G₁ + G₂) = qExpansion h G₁ + qExpansion h G₂ :=
  qExpansion_add (h₁.analyticAt hh) (h₂.analyticAt hh)

theorem qExpansion_pow_of_good (hh : 0 < h) (hG : Good h G) :
    ∀ n : ℕ, qExpansion h (G ^ n) = qExpansion h G ^ n
  | 0 => by rw [pow_zero, pow_zero, qExpansion_one]
  | n + 1 => by rw [pow_succ, pow_succ, qExpansion_mul_of_good hh (hG.pow n) hG,
      qExpansion_pow_of_good hh hG n]

theorem qExpansion_const (hh : 0 < h) (c : ℂ) : qExpansion h (fun _ : ℍ => c) = PowerSeries.C c := by
  have h1 : (fun _ : ℍ => c) = c • (1 : ℍ → ℂ) := by funext τ; simp
  rw [h1, qExpansion_smul ((Good.one h).analyticAt hh), qExpansion_one, Algebra.smul_def, mul_one]
  simp

theorem Good.eq_zero_of_qExpansion_eq_zero (hG : Good h G) (hh : 0 < h) (h0 : qExpansion h G = 0) :
    G = 0 :=
  (qExpansion_eq_zero_iff hh hG.periodic hG.mdiff hG.bdd).mp h0

def Q (h : ℝ) (G : ℍ → ℂ) : LaurentSeries ℂ := HahnSeries.ofPowerSeries ℤ ℂ (qExpansion h G)

theorem Q_mul (hh : 0 < h) (h₁ : Good h G₁) (h₂ : Good h G₂) : Q h (G₁ * G₂) = Q h G₁ * Q h G₂ := by
  simp only [Q, qExpansion_mul_of_good hh h₁ h₂, map_mul]

theorem Q_add (hh : 0 < h) (h₁ : Good h G₁) (h₂ : Good h G₂) : Q h (G₁ + G₂) = Q h G₁ + Q h G₂ := by
  simp only [Q, qExpansion_add_of_good hh h₁ h₂, map_add]

theorem Q_pow (hh : 0 < h) (hG : Good h G) (n : ℕ) : Q h (G ^ n) = Q h G ^ n := by
  simp only [Q, qExpansion_pow_of_good hh hG n, map_pow]

theorem Q_one (h : ℝ) : Q h (1 : ℍ → ℂ) = 1 := by
  simp only [Q, qExpansion_one, map_one]

theorem Q_const (hh : 0 < h) (c : ℂ) : Q h (fun _ : ℍ => c) = HahnSeries.C c := by
  simp only [Q, qExpansion_const hh c, HahnSeries.ofPowerSeries_C]

theorem Q_eq_zero_iff (hh : 0 < h) (hG : Good h G) : Q h G = 0 ↔ G = 0 := by
  constructor
  · intro h0
    apply hG.eq_zero_of_qExpansion_eq_zero hh
    have : Function.Injective (HahnSeries.ofPowerSeries ℤ ℂ) := HahnSeries.ofPowerSeries_injective
    exact this (by rw [map_zero]; exact h0)
  · rintro rfl
    simp only [Q, qExpansion_zero, map_zero]

end Toolkit

section LevelOne

local notation "Δ" => ModularForm.discriminant

theorem natCast_mem_strictPeriods (N : ℕ) : (N : ℝ) ∈ (𝒮ℒ).strictPeriods := by
  simp only [Subgroup.strictPeriods_SL2Z]
  exact ⟨N, by simp⟩

theorem good_discriminant (N : ℕ) : Good N Δ where
  periodic := by
    have := SlashInvariantFormClass.periodic_comp_ofComplex CuspForm.discriminant
      (natCast_mem_strictPeriods N)
    simpa using this
  mdiff := CuspForm.discriminant.holo'
  bdd := ModularForm.discriminant_isZeroAtImInfty.isBoundedAtImInfty

theorem good_E₄ (N : ℕ) : Good N (ModularForm.E₄ : ℍ → ℂ) where
  periodic := SlashInvariantFormClass.periodic_comp_ofComplex ModularForm.E₄
      (natCast_mem_strictPeriods N)
  mdiff := ModularForm.E₄.holo'
  bdd := ModularFormClass.bdd_at_infty ModularForm.E₄

theorem discriminant_ne_zero' : (Δ : ℍ → ℂ) ≠ 0 := by
  intro h0
  have := congrFun h0 UpperHalfPlane.I
  exact ModularForm.discriminant_ne_zero _ this

theorem discriminant_pow_ne_zero (m : ℕ) : ((Δ : ℍ → ℂ) ^ m) ≠ 0 := by
  intro h0
  have := congrFun h0 UpperHalfPlane.I
  simp only [Pi.pow_apply, Pi.zero_apply, pow_eq_zero_iff', ne_eq] at this
  exact ModularForm.discriminant_ne_zero _ this.1

theorem mul_discriminant_pow_eq_zero_iff (F : ℍ → ℂ) (m : ℕ) :
    F * (Δ : ℍ → ℂ) ^ m = 0 ↔ F = 0 := by
  constructor
  · intro h0
    funext τ
    have := congrFun h0 τ
    simp only [Pi.mul_apply, Pi.pow_apply, Pi.zero_apply, mul_eq_zero, pow_eq_zero_iff',
      ne_eq] at this
    rcases this with h1 | ⟨h1, _⟩
    · exact h1
    · exact absurd h1 (ModularForm.discriminant_ne_zero τ)
  · rintro rfl
    exact zero_mul _

theorem Q_discriminant_ne_zero (N : ℕ) [NeZero N] : Q N (Δ : ℍ → ℂ) ≠ 0 := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  rw [ne_eq, Q_eq_zero_iff hN (good_discriminant N)]
  exact discriminant_ne_zero'

end LevelOne

section Ring

local notation "Δ" => ModularForm.discriminant

variable (N : ℕ) [NeZero N]

theorem mdifferentiable_of_mem {F : ℍ → ℂ} (hF : F ∈ ring N) : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F := by
  have h := WLight.levelN_structure_package N PeriodPair.ofTau (fun τ => ⟨rfl, rfl⟩) (wp N)
    (fun v τ => rfl) (fricke N) (fun v τ => rfl) jAnalytic (fun τ => rfl)
  exact h.2.2.2.2.1 F hF

theorem eq_zero_or_eq_zero_of_mul_eq_zero {a b : ℍ → ℂ} (ha : a ∈ ring N) (hb : b ∈ ring N)
    (hab : a * b = 0) : a = 0 ∨ b = 0 := by
  have h := WLight.levelN_structure_package N PeriodPair.ofTau (fun τ => ⟨rfl, rfl⟩) (wp N)
    (fun v τ => rfl) (fricke N) (fun v τ => rfl) jAnalytic (fun τ => rfl)
  exact h.2.2.2.2.2 a b ha hb hab

abbrev redMat (γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) (ZMod N) :=
  (γ : Matrix (Fin 2) (Fin 2) ℤ).map ((↑) : ℤ → ZMod N)

theorem fricke_smul_of_mem (v : Fin 2 → ZMod N) {γ : SL(2, ℤ)}
    (hγ : γ ∈ CongruenceSubgroup.Gamma N) (τ : ℍ) : fricke N v (γ • τ) = fricke N v τ :=
  (WLight.frickeFunction_modularity_package N PeriodPair.ofTau (fun _ => ⟨rfl, rfl⟩)).2.2.2.2.2.2.1
    v γ hγ τ

omit [NeZero N] in

theorem jAnalytic_smul (γ : SL(2, ℤ)) (τ : ℍ) : jAnalytic (γ • τ) = jAnalytic τ := by
  have hmem : (γ : GL (Fin 2) ℝ) ∈ 𝒮ℒ := ⟨γ, rfl⟩
  have h4 : (ModularForm.E₄ : ℍ → ℂ) ((γ : GL (Fin 2) ℝ) • τ) =
      denom (γ : GL (Fin 2) ℝ) τ ^ (4 : ℤ) * ModularForm.E₄ τ :=
    SlashInvariantForm.slash_action_eqn'' _ hmem τ
  have h12 : ModularForm.discriminant ((γ : GL (Fin 2) ℝ) • τ) =
      denom (γ : GL (Fin 2) ℝ) τ ^ (12 : ℤ) * ModularForm.discriminant τ := by
    have := SlashInvariantForm.slash_action_eqn'' CuspForm.discriminant hmem τ
    simpa using this
  have hd : denom (γ : GL (Fin 2) ℝ) τ ≠ 0 := denom_ne_zero _ _
  have hΔ : ModularForm.discriminant τ ≠ 0 := ModularForm.discriminant_ne_zero τ
  rw [jAnalytic, jAnalytic, ModularGroup.sl_moeb, h4, h12]
  field_simp

def precomp (g : SL(2, ℤ)) : (ℍ → ℂ) →ₐ[ℂ] (ℍ → ℂ) :=
  -- Pin: `Pi.algHom ℂ (fun _ : ℍ => ℂ) (fun τ => Pi.evalAlgHom ℂ (fun _ : ℍ => ℂ) (g • τ))`;
  -- `Pi.algHom` is a deprecated alias for `AlgHom.pi` in mathlib `v4.34.0`.
  AlgHom.pi fun τ => Pi.evalAlgHom ℂ (fun _ : ℍ => ℂ) (g • τ)

omit [NeZero N] in
@[scoped simp]
theorem precomp_apply (g : SL(2, ℤ)) (F : ℍ → ℂ) (τ : ℍ) : precomp g F τ = F (g • τ) := rfl

theorem smul_eq_self_of_mem {F : ℍ → ℂ} (hF : F ∈ ring N) {γ : SL(2, ℤ)}
    (hγ : γ ∈ CongruenceSubgroup.Gamma N) (τ : ℍ) : F (γ • τ) = F τ := by

  suffices h : ring N ≤ AlgHom.equalizer (precomp γ) (AlgHom.id ℂ (ℍ → ℂ)) by
    have := h hF
    rw [AlgHom.mem_equalizer] at this
    exact congrFun this τ
  rw [ring, Algebra.adjoin_le_iff]
  intro G hG
  rw [SetLike.mem_coe, AlgHom.mem_equalizer]
  funext τ'
  rcases hG with rfl | ⟨v, hv, rfl⟩
  · exact jAnalytic_smul γ τ'
  · exact fricke_smul_of_mem N v hγ τ'

omit [NeZero N] in
theorem T_pow_mem_Gamma : ModularGroup.T ^ N ∈ CongruenceSubgroup.Gamma N := by
  rw [CongruenceSubgroup.Gamma_mem, ← zpow_natCast, ModularGroup.coe_T_zpow]
  simp

theorem periodic_of_mem {F : ℍ → ℂ} (hF : F ∈ ring N) : Periodic (F ∘ ofComplex) N := by
  intro w
  by_cases hw : 0 < w.im
  · have hw' : 0 < (w + N).im := by simpa using hw
    simp only [Function.comp_apply, ofComplex_apply_of_im_pos hw, ofComplex_apply_of_im_pos hw']
    have hT : ModularGroup.T ^ N • (⟨w, hw⟩ : ℍ) = ⟨w + N, hw'⟩ := by
      rw [← zpow_natCast, modular_T_zpow_smul]
      ext1
      simp [add_comm]
    rw [← hT, smul_eq_self_of_mem N hF (T_pow_mem_Gamma N)]
  · push Not at hw
    have hw' : (w + N).im ≤ 0 := by simpa using hw
    simp only [Function.comp_apply, ofComplex_apply_of_im_nonpos hw,
      ofComplex_apply_of_im_nonpos hw']

theorem exists_isBoundedAtImInfty_mul_pow {F : ℍ → ℂ} (hF : F ∈ ring N) :
    ∃ m : ℕ, IsBoundedAtImInfty (F * (Δ : ℍ → ℂ) ^ m) := by
  have hpkg := WLight.frickeFunction_orbit_package N PeriodPair.ofTau (fun τ => ⟨rfl, rfl⟩) (wp N)
    (fun v τ => rfl) (fricke N) (fun v τ => rfl) jAnalytic (fun τ => rfl)
  have hΔb : ∀ k : ℕ, IsBoundedAtImInfty ((Δ : ℍ → ℂ) ^ k) := fun k =>
    ((good_discriminant N).pow k).bdd
  induction hF using Algebra.adjoin_induction with
  | mem G hG =>
    rcases hG with rfl | ⟨v, hv, rfl⟩
    · exact hpkg.1.2
    · exact (hpkg.2.1 v hv).2
  | algebraMap c =>
    refine ⟨0, ?_⟩
    rw [pow_zero, mul_one]
    exact Filter.const_boundedAtFilter _ _
  | add F G _ _ ihF ihG =>
    obtain ⟨m, hm⟩ := ihF
    obtain ⟨n, hn⟩ := ihG
    refine ⟨m + n, ?_⟩
    have : (F + G) * (Δ : ℍ → ℂ) ^ (m + n) =
        F * (Δ : ℍ → ℂ) ^ m * (Δ : ℍ → ℂ) ^ n + G * (Δ : ℍ → ℂ) ^ n * (Δ : ℍ → ℂ) ^ m := by ring
    rw [this]
    exact (hm.mul (hΔb n)).add (hn.mul (hΔb m))
  | mul F G _ _ ihF ihG =>
    obtain ⟨m, hm⟩ := ihF
    obtain ⟨n, hn⟩ := ihG
    refine ⟨m + n, ?_⟩
    have : (F * G) * (Δ : ℍ → ℂ) ^ (m + n) = (F * (Δ : ℍ → ℂ) ^ m) * (G * (Δ : ℍ → ℂ) ^ n) := by
      ring
    rw [this]
    exact hm.mul hn

end Ring

section Expansion

local notation "Δ" => ModularForm.discriminant

variable (N : ℕ) [NeZero N]

theorem castN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)

def PB (F : ℍ → ℂ) (m : ℕ) : Prop := IsBoundedAtImInfty (F * (Δ : ℍ → ℂ) ^ m)

theorem PB.add_right {F : ℍ → ℂ} {m : ℕ} (hm : PB F m) (k : ℕ) : PB F (m + k) := by
  unfold PB at hm ⊢
  rw [pow_add, ← mul_assoc]
  exact hm.mul ((good_discriminant 1).pow k).bdd

theorem good_of_PB {F : ℍ → ℂ} (hF : F ∈ ring N) {m : ℕ} (hm : PB F m) :
    Good N (F * (Δ : ℍ → ℂ) ^ m) where
  periodic := by
    have : (F * (Δ : ℍ → ℂ) ^ m) ∘ ofComplex = (F ∘ ofComplex) * (((Δ : ℍ → ℂ) ^ m) ∘ ofComplex) := rfl
    rw [this]
    exact (periodic_of_mem N hF).mul ((good_discriminant N).pow m).periodic
  mdiff := (mdifferentiable_of_mem N hF).mul ((good_discriminant N).pow m).mdiff
  bdd := hm

end Expansion

section Width

variable (N : ℕ) [NeZero N]

theorem qParam_pow_mul (τ : ℍ) (n : ℕ) :
    Periodic.qParam (N : ℝ) (τ : ℂ) ^ (N * n) = Periodic.qParam 1 (τ : ℂ) ^ n := by
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  rw [pow_mul]
  congr 1
  rw [Periodic.qParam, Periodic.qParam, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp

theorem Q_natCast_eq_qExpand {f : ℍ → ℂ} (hf : Good 1 f) :
    Q N f = ModularCurve.qExpand ℂ N (Q 1 f) := by
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  have hN0 : (N : ℕ) ≠ 0 := NeZero.ne N
  set a : ℕ → ℂ := fun m => (qExpansion 1 f).coeff m with ha
  have hsum1 : ∀ τ : ℍ, HasSum (fun m => a m • Periodic.qParam 1 (τ : ℂ) ^ m) (f τ) :=
    fun τ => hasSum_qExpansion one_pos hf.periodic hf.mdiff hf.bdd τ
  have hinj : Function.Injective (fun n : ℕ => N * n) := mul_right_injective₀ hN0
  set c : ℕ → ℂ := Function.extend (fun n : ℕ => N * n) a 0 with hc
  have hc_apply : ∀ n, c (N * n) = a n := fun n => hinj.extend_apply _ _ n
  have hc_zero : ∀ m, (¬ ∃ n, N * n = m) → c m = 0 := fun m hm => by
    rw [hc, Function.extend_apply' _ _ _ hm]; rfl
  have hsumN : ∀ τ : ℍ, HasSum (fun m => c m • Periodic.qParam (N : ℝ) (τ : ℂ) ^ m) (f τ) := by
    intro τ
    have key : (fun m => c m • Periodic.qParam (N : ℝ) (τ : ℂ) ^ m) =
        Function.extend (fun n : ℕ => N * n) (fun n => a n • Periodic.qParam 1 (τ : ℂ) ^ n) 0 := by
      funext m
      by_cases hm : ∃ n, N * n = m
      · obtain ⟨n, rfl⟩ := hm
        rw [hinj.extend_apply, hc_apply, qParam_pow_mul]
      · rw [Function.extend_apply' _ _ _ hm, hc_zero m hm, zero_smul]; rfl
    rw [key, hasSum_extend_zero hinj]
    exact hsum1 τ
  have hgoodN : Good N f :=
    { periodic := by simpa using hf.periodic.nat_mul N
      mdiff := hf.mdiff
      bdd := hf.bdd }
  have hcoeff : ∀ m, c m = (qExpansion N f).coeff m := by
    have hsumN' : ∀ τ : ℍ, HasSum (fun m => (qExpansion N f).coeff m • Periodic.qParam (N : ℝ) (τ : ℂ) ^ m) (f τ) :=
      fun τ => hasSum_qExpansion hNpos hgoodN.periodic hgoodN.mdiff hgoodN.bdd τ
    have h1 := (hasFPowerSeriesOnBall_cuspFunction hNpos (hgoodN.analyticAt hNpos) hsumN).hasFPowerSeriesAt
    have h2 := (hasFPowerSeriesOnBall_cuspFunction hNpos (hgoodN.analyticAt hNpos) hsumN').hasFPowerSeriesAt
    have heq := h1.eq_formalMultilinearSeries h2
    have := (FormalMultilinearSeries.ofScalars_series_eq_iff (E := ℂ) c _).mp heq
    exact fun m => congrFun this m

  ext k
  rw [Q, Q]
  rcases lt_or_ge k 0 with hk | hk
  · rw [ModularCurve.ofPowerSeries_coeff_of_neg _ hk]
    by_cases hdvd : (N : ℤ) ∣ k
    · obtain ⟨k', rfl⟩ := hdvd
      rw [ModularCurve.qExpand_coeff_mul]
      have hk' : k' < 0 := by
        by_contra h; push Not at h
        have : (0 : ℤ) ≤ (N : ℤ) * k' := mul_nonneg (by positivity) h
        omega
      rw [ModularCurve.ofPowerSeries_coeff_of_neg _ hk']
    · rw [ModularCurve.qExpand_coeff_of_not_dvd N _ hdvd]
  · lift k to ℕ using hk
    rw [HahnSeries.ofPowerSeries_apply_coeff, ← hcoeff]
    by_cases hdvd : (N : ℤ) ∣ (k : ℤ)
    · obtain ⟨k', hk'⟩ := hdvd
      have hk'0 : 0 ≤ k' := by
        by_contra h; push Not at h
        have : (N : ℤ) * k' < 0 := mul_neg_of_pos_of_neg (by exact_mod_cast NeZero.pos N) h
        omega
      lift k' to ℕ using hk'0
      have hkk : k = N * k' := by exact_mod_cast hk'
      rw [hk', ModularCurve.qExpand_coeff_mul, HahnSeries.ofPowerSeries_apply_coeff, hkk, hc_apply]
    · rw [ModularCurve.qExpand_coeff_of_not_dvd N _ hdvd, hc_zero]
      rintro ⟨n, hn⟩
      exact hdvd ⟨n, by rw [← hn]; push_cast; ring⟩

end Width
end LevelN

end ModularCurve

end
