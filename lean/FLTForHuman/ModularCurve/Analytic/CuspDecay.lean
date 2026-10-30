/-
  Cusp decay under integrality: the `E₄²E₆`-versus-`Δ` comparison at `i∞`.

  Statement verbatim from
  `Theorems/Thm_ModularCurve_eventually_norm_slash_le_of_isIntegral_adjoin_jqModC_inv_pow.lean`,
  proof transcribed from
  `P2M/Sol/S_ModularCurve_eventually_norm_slash_le_of_isIntegral_adjoin_jqModC_inv_pow.lean`
  (734 lines, 53 declarations), pin `aa2d8b3`.

  The row says: if `X = g/h` as `q`-expansions and the monic integrality witness
  `X ^ (2M) · j ^ (mM+1) · (j - 1728) ^ (mM)` is integral over `ℂ[j⁻¹]`, then the slash of
  `g · (E₄²E₆)^m` by any `A ∈ SL(2, ℤ)` is eventually dominated at the cusp by `ε` times the
  slash of `h · Δ^m`, in weights `k + 14m` and `k + 12m` respectively.  The engine is
  `coreC`: the integrality witness turns into a *monic* polynomial relation
  `U ^ n + ∑ κᵢ U ^ i = 0` for `U = u/v` at a point `z = A • τ`, and
  `norm_le_of_monic_relation` bounds `‖U‖` by the coefficient bound; the growth of `Δ`
  against `E₄²E₆` at the cusp then pins the two sides down.

  **Reuse.**  The pin's `ANb` block (its lines 22–490) — `Nice`, `niceSubalgebra`, `ψ`,
  `toC`, `ofMF`, `nice_of_modularForm`, `𝔞`, `𝔟`, `𝔡`, the coefficient facts
  `qA0`/`qA1`/`qB0`/`qB1`/`qD1` and the identities `A_cube_sub_B_sq`, `J_mul_D`,
  `J_sub_mul_D`, `coeffEmb_jq` — is already public in
  `FLTForHuman/ModularCurve/Analytic/ANb.lean`, which this module imports; it is *not*
  restated here.  What is transcribed is the pin's second `ANb` block that `ANb.lean` does
  not carry (`ψ𝔞_ne_zero`, `J_ne_zero`, `Jinv_mul_A_cube`, `ev`, `slash_coe_apply`,
  `levelOne_apply_smul`, the three `_apply_smul` slash formulas, `tendsto_nice`,
  `norm_le_of_monic_relation`, `coreC`) plus the headline.  Those are `private` — the row's
  public surface is the headline alone.

  The pin's `set_option maxHeartbeats 3200000 in` above its `solution` (its line 494) is
  **not** transcribed (FR-0067: the port has never needed a pin cap), and neither are its
  `p2m_open`/`p2m_reactivate` plumbing or its `attribute [-simp]` preludes.  Every
  declaration fits the project's 200,000-heartbeat edit loop without a local cap.

  FLT provenance, pinned `aa2d8b3`:
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_eventually_norm_slash_le_of_isIntegral_adjoin_jqModC_inv_pow.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_eventually_norm_slash_le_of_isIntegral_adjoin_jqModC_inv_pow.lean

spec-pin: Theorems/Thm_ModularCurve_eventually_norm_slash_le_of_isIntegral_adjoin_jqModC_inv_pow.lean
spec-pin: P2M/Sol/S_ModularCurve_eventually_norm_slash_le_of_isIntegral_adjoin_jqModC_inv_pow.lean
-/

import FLTForHuman.ModularCurve.Analytic.ANb
import FLTForHuman.ModularCurve.JqIntegralRatios
import FLTForHuman.ModularForms.JqAnalyticModel
import FLTForHuman.ModularForms.QCoeffLevelOne
import FLTForHuman.ModularCurve.Analytic.QParamUnique
import FLTForHuman.ModularForms.HeckeQCoeff

set_option autoImplicit false

noncomputable section

open UpperHalfPlane ModularCurve _root_.Polynomial
open scoped MatrixGroups ModularForm Manifold

namespace ANb

local notation "𝒩" => niceSubalgebra
local notation "𝐉" => ModularCurve.coeffEmb ℂ ModularCurve.jq

theorem ψ𝔞_ne_zero : ψ 𝔞 ≠ 0 := by
  intro h
  have h0 : qExpansion 1 (ModularForm.E₄ : ℍ → ℂ) = 0 :=
    HahnSeries.ofPowerSeries_injective (by rw [← ψ𝔞, h, map_zero])
  have := qA0
  rw [h0, map_zero] at this
  exact zero_ne_one this

theorem J_ne_zero : (𝐉) ≠ 0 := by
  intro h
  have := J_mul_D
  rw [h, zero_mul] at this
  exact pow_ne_zero 3 ψ𝔞_ne_zero this.symm

theorem Jinv_mul_A_cube : (𝐉)⁻¹ * ψ 𝔞 ^ 3 = ψ 𝔡 := by
  rw [← J_mul_D, ← mul_assoc, inv_mul_cancel₀ J_ne_zero, one_mul]

def ev (z : ℍ) : 𝒩 →ₐ[ℂ] ℂ where
  toFun f := (f : ℍ → ℂ) z
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

theorem ev_apply (z : ℍ) (f : 𝒩) : ev z f = (f : ℍ → ℂ) z := rfl

theorem slash_coe_apply (f : ℍ → ℂ) (k : ℤ) (A : SL(2, ℤ)) (τ : ℍ) :
    (f ∣[k] (A : GL (Fin 2) ℝ)) τ = f (A • τ) * denom (A : GL (Fin 2) ℝ) τ ^ (-k) := by
  rw [← ModularForm.SL_slash]
  exact ModularForm.SL_slash_apply f A τ

theorem levelOne_apply_smul {k : ℤ} {F : Type*} [FunLike F ℍ ℂ]
    [SlashInvariantFormClass F 𝒮ℒ k] (f : F) (A : SL(2, ℤ)) (τ : ℍ) :
    f (A • τ) = denom (A : GL (Fin 2) ℝ) τ ^ k * f τ := by
  have h1 := congrFun (SlashInvariantForm.slash_action_eqn f (A : GL (Fin 2) ℝ) ⟨A, rfl⟩) τ
  rw [slash_coe_apply] at h1
  have hδ := denom_ne_zero (A : GL (Fin 2) ℝ) τ
  calc f (A • τ) = f (A • τ) * denom (A : GL (Fin 2) ℝ) τ ^ (-k) * denom (A : GL (Fin 2) ℝ) τ ^ k := by
        rw [mul_assoc, ← zpow_add₀ hδ, neg_add_cancel, zpow_zero, mul_one]
    _ = denom (A : GL (Fin 2) ℝ) τ ^ k * f τ := by rw [h1, mul_comm]

theorem 𝔞_apply_smul (A : SL(2, ℤ)) (τ : ℍ) :
    (𝔞 : ℍ → ℂ) (A • τ) = denom (A : GL (Fin 2) ℝ) τ ^ 4 * (𝔞 : ℍ → ℂ) τ := by
  have := levelOne_apply_smul ModularForm.E₄ A τ
  simp only [zpow_ofNat] at this
  exact this
theorem 𝔟_apply_smul (A : SL(2, ℤ)) (τ : ℍ) :
    (𝔟 : ℍ → ℂ) (A • τ) = denom (A : GL (Fin 2) ℝ) τ ^ 6 * (𝔟 : ℍ → ℂ) τ := by
  have := levelOne_apply_smul ModularForm.E₆ A τ
  simp only [zpow_ofNat] at this
  exact this
theorem 𝔡_apply_smul (A : SL(2, ℤ)) (τ : ℍ) :
    (𝔡 : ℍ → ℂ) (A • τ) = denom (A : GL (Fin 2) ℝ) τ ^ 12 * (𝔡 : ℍ → ℂ) τ := by
  have := levelOne_apply_smul CuspForm.discriminant A τ
  simp only [zpow_ofNat] at this
  exact this

theorem tendsto_nice (f : 𝒩) :
    Filter.Tendsto (f : ℍ → ℂ) atImInfty (nhds (PowerSeries.coeff 0 (qExpansion 1 (f : ℍ → ℂ)))) := by
  refine ModularCurve.tendsto_atImInfty_of_hasSum_qParam 1 one_pos (f : ℍ → ℂ)
    (fun m => PowerSeries.coeff m (qExpansion 1 (f : ℍ → ℂ))) fun τ => ?_
  have := UpperHalfPlane.hasSum_qExpansion one_pos f.2.1 f.2.2.1 f.2.2.2 τ
  simpa [smul_eq_mul] using this

theorem norm_le_of_monic_relation {n : ℕ} {u : ℂ} {κ : ℕ → ℂ} {B : ℝ} (hB : 0 ≤ B)
    (hκ : ∀ i ∈ Finset.range n, ‖κ i‖ ≤ B) (h : u ^ n + ∑ i ∈ Finset.range n, κ i * u ^ i = 0) :
    ‖u‖ ≤ n * B + 1 := by
  have hnB : 0 ≤ (n : ℝ) * B := mul_nonneg n.cast_nonneg hB
  by_cases hu' : ‖u‖ ≤ 1
  · linarith
  have hu : 1 < ‖u‖ := not_le.mp hu'
  have hn : n ≠ 0 := by
    rintro rfl
    simp at h
  obtain ⟨n', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  have hun : u ^ (n' + 1) = -∑ i ∈ Finset.range (n' + 1), κ i * u ^ i := eq_neg_of_add_eq_zero_left h
  have hle : ‖u‖ ^ (n' + 1) ≤ (n' + 1 : ℕ) * B * ‖u‖ ^ n' := by
    calc ‖u‖ ^ (n' + 1) = ‖u ^ (n' + 1)‖ := (norm_pow _ _).symm
      _ = ‖∑ i ∈ Finset.range (n' + 1), κ i * u ^ i‖ := by rw [hun, norm_neg]
      _ ≤ ∑ i ∈ Finset.range (n' + 1), ‖κ i * u ^ i‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.range (n' + 1), B * ‖u‖ ^ n' := by
          refine Finset.sum_le_sum fun i hi => ?_
          rw [norm_mul, norm_pow]
          have hi' : i ≤ n' := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
          exact mul_le_mul (hκ i hi) (pow_le_pow_right₀ hu.le hi') (pow_nonneg (norm_nonneg _) _) hB
      _ = (n' + 1 : ℕ) * B * ‖u‖ ^ n' := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
  have hpos : 0 < ‖u‖ ^ n' := pow_pos (by linarith) _
  rw [pow_succ, mul_comm] at hle
  have := le_of_mul_le_mul_right hle hpos
  linarith

theorem coreC (𝔤 𝔥 : 𝒩) (X : LaurentSeries ℂ) (hX : X * ψ 𝔥 = ψ 𝔤) (M w : ℕ)
    (h₂ : IsIntegral (Algebra.adjoin ℂ ({(𝐉)⁻¹} : Set (LaurentSeries ℂ)))
      (X ^ (2 * M) * 𝐉 ^ (w * M + 1) * (𝐉 - algebraMap ℂ (LaurentSeries ℂ) 1728) ^ (w * M))) :
    ∃ (n m : ℕ) (K : ℕ → 𝒩),
      (∀ i ∈ Finset.range n, ∀ (A : SL(2, ℤ)) (τ : ℍ), (K i : ℍ → ℂ) (A • τ) =
          denom (A : GL (Fin 2) ℝ) τ ^ (12 * m) * (K i : ℍ → ℂ) τ) ∧
      (𝔤 ^ (2 * M) * 𝔞 ^ (3 * (w * M) + 3) * 𝔟 ^ (2 * (w * M))) ^ n * 𝔞 ^ (3 * m) +
        ∑ i ∈ Finset.range n, K i * ((𝔤 ^ (2 * M) * 𝔞 ^ (3 * (w * M) + 3) * 𝔟 ^ (2 * (w * M))) ^ i *
          (𝔥 ^ (2 * M) * 𝔡 ^ (2 * (w * M) + 1)) ^ (n - i)) = 0 := by
  classical

  have key1 : (X ^ (2 * M) * 𝐉 ^ (w * M + 1) * (𝐉 - algebraMap ℂ (LaurentSeries ℂ) 1728) ^ (w * M)) *
      (ψ 𝔥 ^ (2 * M) * ψ 𝔡 ^ (2 * (w * M) + 1)) = ψ 𝔤 ^ (2 * M) * ψ 𝔞 ^ (3 * (w * M) + 3) * ψ 𝔟 ^ (2 * (w * M)) := by
    calc (X ^ (2 * M) * 𝐉 ^ (w * M + 1) * (𝐉 - algebraMap ℂ (LaurentSeries ℂ) 1728) ^ (w * M)) *
          (ψ 𝔥 ^ (2 * M) * ψ 𝔡 ^ (2 * (w * M) + 1))
        = (X * ψ 𝔥) ^ (2 * M) * (𝐉 * ψ 𝔡) ^ (w * M + 1) * ((𝐉 - algebraMap ℂ (LaurentSeries ℂ) 1728) * ψ 𝔡) ^ (w * M) := by
          rw [mul_pow (𝐉 - algebraMap ℂ (LaurentSeries ℂ) 1728) (ψ 𝔡) (w * M), mul_pow X (ψ 𝔥), mul_pow (𝐉) (ψ 𝔡)]
          ring
      _ = (ψ 𝔤) ^ (2 * M) * (ψ 𝔞 ^ 3) ^ (w * M + 1) * (ψ 𝔟 ^ 2) ^ (w * M) := by rw [hX, J_mul_D, J_sub_mul_D]
      _ = ψ 𝔤 ^ (2 * M) * ψ 𝔞 ^ (3 * (w * M) + 3) * ψ 𝔟 ^ (2 * (w * M)) := by
          rw [← pow_mul, ← pow_mul, show 3 * (w * M + 1) = 3 * (w * M) + 3 by ring]

  obtain ⟨p, hpm, hpev⟩ := h₂
  rw [hpm.as_sum] at hpev
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_finsetSum,
    Polynomial.eval₂_mul, Polynomial.eval₂_C] at hpev
  set R := Algebra.adjoin ℂ ({(𝐉)⁻¹} : Set (LaurentSeries ℂ)) with hR
  set Y := X ^ (2 * M) * 𝐉 ^ (w * M + 1) * (𝐉 - algebraMap ℂ (LaurentSeries ℂ) 1728) ^ (w * M) with hY
  set n := p.natDegree with hn
  clear_value Y
  have hmem : ∀ i, ∃ c : Polynomial ℂ,
      Polynomial.aeval ((𝐉)⁻¹) c = algebraMap R (LaurentSeries ℂ) (p.coeff i) := by
    intro i
    have hi' : algebraMap R (LaurentSeries ℂ) (p.coeff i) ∈ (Polynomial.aeval (R := ℂ) ((𝐉)⁻¹)).range := by
      rw [← Algebra.adjoin_singleton_eq_range_aeval]
      exact (p.coeff i).2
    exact hi'
  choose c hc using hmem
  set m := ∑ i ∈ Finset.range n, (c i).natDegree with hm
  have hdeg : ∀ i ∈ Finset.range n, (c i).natDegree ≤ m := fun i hi =>
    Finset.single_le_sum (f := fun j => (c j).natDegree) (fun j _ => Nat.zero_le _) hi
  clear_value m

  let K : ℕ → 𝒩 := fun i =>
    ∑ l ∈ Finset.range ((c i).natDegree + 1), algebraMap ℂ 𝒩 ((c i).coeff l) * (𝔡 ^ l * 𝔞 ^ (3 * (m - l)))
  have key3 : ∀ i ∈ Finset.range n, ψ 𝔞 ^ (3 * m) * algebraMap R (LaurentSeries ℂ) (p.coeff i) = ψ (K i) := by
    intro i hi
    simp only [K, map_sum, map_mul, map_pow, AlgHom.commutes]
    rw [← hc i, Polynomial.aeval_eq_sum_range, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l hl => ?_
    have hlm : l ≤ m := (Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)).trans (hdeg i hi)
    rw [Algebra.smul_def, mul_left_comm]
    congr 1
    calc ψ 𝔞 ^ (3 * m) * (𝐉)⁻¹ ^ l = ψ 𝔞 ^ (3 * (m - l)) * (ψ 𝔞 ^ 3) ^ l * (𝐉)⁻¹ ^ l := by
          rw [← pow_mul, ← pow_add, show 3 * (m - l) + 3 * l = 3 * m by omega]
      _ = ψ 𝔞 ^ (3 * (m - l)) * ((𝐉)⁻¹ * ψ 𝔞 ^ 3) ^ l := by rw [mul_pow ((𝐉)⁻¹)]; ring
      _ = ψ 𝔡 ^ l * ψ 𝔞 ^ (3 * (m - l)) := by rw [Jinv_mul_A_cube, mul_comm]

  let W : 𝒩 := 𝔤 ^ (2 * M) * 𝔞 ^ (3 * (w * M) + 3) * 𝔟 ^ (2 * (w * M))
  let V : 𝒩 := 𝔥 ^ (2 * M) * 𝔡 ^ (2 * (w * M) + 1)
  have k1 : Y * ψ V = ψ W := by
    simp only [W, V, map_mul, map_pow]
    exact key1
  have key2 : ∀ i ≤ n, ψ V ^ n * Y ^ i = ψ W ^ i * ψ V ^ (n - i) := by
    intro i hi
    have e : ψ V ^ n = ψ V ^ i * ψ V ^ (n - i) := by
      rw [← pow_add, Nat.add_sub_cancel' hi]
    calc ψ V ^ n * Y ^ i = (Y * ψ V) ^ i * ψ V ^ (n - i) := by
          rw [e, mul_pow Y (ψ V) i]; ring
      _ = ψ W ^ i * ψ V ^ (n - i) := by rw [k1]

  let E : 𝒩 := W ^ n * 𝔞 ^ (3 * m) + ∑ i ∈ Finset.range n, K i * (W ^ i * V ^ (n - i))
  have hE : ψ E = ψ V ^ n * ψ 𝔞 ^ (3 * m) *
      (Y ^ n + ∑ i ∈ Finset.range n, algebraMap R (LaurentSeries ℂ) (p.coeff i) * Y ^ i) := by
    rw [mul_add, Finset.mul_sum]
    simp only [E, map_add, map_sum, map_mul, map_pow]
    congr 1
    · have h2 := key2 n le_rfl
      rw [Nat.sub_self, pow_zero, mul_one] at h2
      rw [mul_right_comm, h2]
    · refine Finset.sum_congr rfl fun i hi => ?_
      have hin : i ≤ n := (Finset.mem_range.mp hi).le
      rw [← key3 i hi, ← key2 i hin]
      ring
  have hE0 : E = 0 := by
    apply ψ_injective
    rw [hE, hpev, mul_zero, map_zero]
  refine ⟨n, m, K, fun i hi A τ => ?_, hE0⟩

  have hlm : ∀ l ∈ Finset.range ((c i).natDegree + 1), l ≤ m := fun l hl =>
    (Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)).trans (hdeg i hi)
  show ev (A • τ) (K i) = denom (A : GL (Fin 2) ℝ) τ ^ (12 * m) * ev τ (K i)
  simp only [K, map_sum, map_mul, map_pow, AlgHom.commutes, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [ev_apply, ev_apply, ev_apply, ev_apply, 𝔡_apply_smul, 𝔞_apply_smul,
    show 12 * m = 12 * l + 4 * (3 * (m - l)) by have := hlm l hl; omega]
  ring

end ANb

open ANb in
theorem ModularCurve.eventually_norm_slash_le_of_isIntegral_adjoin_jqModC_inv_pow
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (hT : ModularGroup.T ∈ Γ) {k : ℤ} (m : ℕ)
    (hm : 1 ≤ m) (g h : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (hh : h ≠ 0) (X : LaurentSeries ℂ)
    (hX : X * ((UpperHalfPlane.qExpansion 1 (h : UpperHalfPlane → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
      ((UpperHalfPlane.qExpansion 1 (g : UpperHalfPlane → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ))
    (M : ℕ)
    (h₂ : IsIntegral (Algebra.adjoin ℂ ({(ModularCurve.jqModC ℂ)⁻¹} : Set (LaurentSeries ℂ)))
      (X ^ (2 * M) * ModularCurve.jqModC ℂ ^ (m * M + 1) *
        (ModularCurve.jqModC ℂ - algebraMap ℂ (LaurentSeries ℂ) 1728) ^ (m * M)))
    (A : Matrix.SpecialLinearGroup (Fin 2) ℤ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ τ : UpperHalfPlane in UpperHalfPlane.atImInfty,
      ‖((fun z : UpperHalfPlane => g z * (ModularForm.E₄ z ^ 2 * ModularForm.E₆ z) ^ m) ∣[k + 14 * (m : ℤ)] (A : GL (Fin 2) ℝ)) τ‖ ≤
        ε * ‖((fun z : UpperHalfPlane => h z * ModularForm.discriminant z ^ m) ∣[k + 12 * (m : ℤ)] (A : GL (Fin 2) ℝ)) τ‖ := by
  classical
  -- The pin's `hm` and `hh` are statement-level: its proof never uses them.  The binder block
  -- is the checked statement, so they stay; referencing them here keeps the linter quiet
  -- without a `set_option`.
  have _hm : 1 ≤ m := hm
  have _hh : h ≠ 0 := hh

  rw [← ANb.coeffEmb_jq] at h₂

  have h1 : (1 : ℝ) ∈ ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods :=
    ANb.one_mem_strictPeriods_of_T_mem hT
  obtain ⟨n, μ, K, hK, hE⟩ := ANb.coreC (ANb.ofMF g h1) (ANb.ofMF h h1) X hX M m h₂

  let κ0 : ℕ → ℝ := fun i => ‖PowerSeries.coeff 0 (qExpansion 1 (K i : ℍ → ℂ))‖ + 1
  let B : ℝ := 1 + ∑ i ∈ Finset.range n, κ0 i
  have hκ0 : ∀ i, 0 ≤ κ0 i := fun i => by
    dsimp only [κ0]; exact add_nonneg (norm_nonneg _) zero_le_one
  have hB1 : 1 ≤ B := le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => hκ0 i)
  have hκB : ∀ i ∈ Finset.range n, κ0 i ≤ B := fun i hi =>
    (Finset.single_le_sum (f := κ0) (fun j _ => hκ0 j) hi).trans (le_add_of_nonneg_left zero_le_one)
  let B' : ℝ := B * 2 ^ (3 * μ)
  have hB' : 0 ≤ B' := by
    dsimp only [B']; exact mul_nonneg (by linarith) (pow_nonneg (by norm_num) _)
  let C : ℝ := n * B' + 1
  have hC : 1 ≤ C := by
    dsimp only [C]; exact le_add_of_nonneg_left (mul_nonneg (Nat.cast_nonneg n) hB')
  have hC0 : 0 ≤ C := by linarith
  obtain ⟨η₀, hη₀def⟩ : ∃ e : ℝ, e = ε ^ (2 * M) / (2 ^ (3 * (m * M) + 3) * 2 ^ (4 * (m * M)) * (C + 1)) := ⟨_, rfl⟩
  have hη₀ : 0 < η₀ := by
    rw [hη₀def]
    exact div_pos (pow_pos hε _)
      (mul_pos (mul_pos (pow_pos (by norm_num) _) (pow_pos (by norm_num) _)) (by linarith))
  have hCη : C * η₀ * (2 ^ (3 * (m * M) + 3) * 2 ^ (4 * (m * M))) ≤ ε ^ (2 * M) := by
    have e1 : C * η₀ * (2 ^ (3 * (m * M) + 3) * 2 ^ (4 * (m * M))) = ε ^ (2 * M) * (C / (C + 1)) := by
      rw [hη₀def]
      field_simp
    rw [e1]
    have h1 : C / (C + 1) ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
    calc ε ^ (2 * M) * (C / (C + 1)) ≤ ε ^ (2 * M) * 1 := by
          exact mul_le_mul_of_nonneg_left h1 (pow_nonneg hε.le _)
      _ = ε ^ (2 * M) := mul_one _

  have t4 : Filter.Tendsto (fun τ : ℍ => ModularForm.E₄ τ) atImInfty (nhds 1) := by
    have := ANb.tendsto_nice ANb.𝔞
    rwa [show PowerSeries.coeff 0 (qExpansion 1 ((ANb.𝔞 : ℍ → ℂ))) = 1 from ANb.qA0] at this
  have t6 : Filter.Tendsto (fun τ : ℍ => ModularForm.E₆ τ) atImInfty (nhds 1) := by
    have := ANb.tendsto_nice ANb.𝔟
    rwa [show PowerSeries.coeff 0 (qExpansion 1 ((ANb.𝔟 : ℍ → ℂ))) = 1 from ANb.qB0] at this
  have tΔ : Filter.Tendsto ModularForm.discriminant atImInfty (nhds 0) :=
    ModularForm.discriminant_isZeroAtImInfty
  have e4 : ∀ᶠ τ : ℍ in atImInfty, dist (ModularForm.E₄ τ) 1 < 1 / 2 :=
    Metric.tendsto_nhds.mp t4 _ (by norm_num)
  have e6 : ∀ᶠ τ : ℍ in atImInfty, dist (ModularForm.E₆ τ) 1 < 1 / 2 :=
    Metric.tendsto_nhds.mp t6 _ (by norm_num)
  have eΔ : ∀ᶠ τ : ℍ in atImInfty, dist (ModularForm.discriminant τ) 0 < η₀ :=
    Metric.tendsto_nhds.mp tΔ _ hη₀
  have eK : ∀ᶠ τ : ℍ in atImInfty, ∀ i ∈ Finset.range n, ‖(K i : ℍ → ℂ) τ‖ ≤ κ0 i := by
    refine (Filter.eventually_all_finset _).mpr fun i _ => ?_
    have := Metric.tendsto_nhds.mp (ANb.tendsto_nice (K i)) 1 one_pos
    filter_upwards [this] with τ hτ
    rw [dist_eq_norm] at hτ
    exact (norm_le_insert' _ _).trans (by simp only [κ0]; linarith)
  filter_upwards [e4, e6, eΔ, eK] with τ h4 h6 hd hKτ

  rw [dist_eq_norm] at h4 h6
  rw [dist_zero_right] at hd
  set δ : ℂ := denom (A : GL (Fin 2) ℝ) τ with hδdef
  have hδ : δ ≠ 0 := denom_ne_zero _ _
  set a : ℂ := ModularForm.E₄ τ with ha
  set b : ℂ := ModularForm.E₆ τ with hb
  set d : ℂ := ModularForm.discriminant τ with hdd
  have ha_lo : 1 / 2 < ‖a‖ := by
    have := norm_le_insert' (1 : ℂ) a; rw [norm_one, norm_sub_rev] at this; linarith
  have ha_hi : ‖a‖ < 3 / 2 := by
    have := norm_le_insert' a (1 : ℂ); rw [norm_one] at this; linarith
  have hb_lo : 1 / 2 < ‖b‖ := by
    have := norm_le_insert' (1 : ℂ) b; rw [norm_one, norm_sub_rev] at this; linarith
  have ha0 : a ≠ 0 := fun h0 => by rw [h0, norm_zero] at ha_lo; linarith
  have hb0 : b ≠ 0 := fun h0 => by rw [h0, norm_zero] at hb_lo; linarith
  have hd0 : d ≠ 0 := ModularForm.discriminant_ne_zero τ

  set z : ℍ := A • τ with hz
  have hE4z : ModularForm.E₄ z = δ ^ 4 * a := ANb.𝔞_apply_smul A τ
  have hE6z : ModularForm.E₆ z = δ ^ 6 * b := ANb.𝔟_apply_smul A τ
  have hΔz : ModularForm.discriminant z = δ ^ 12 * d := ANb.𝔡_apply_smul A τ
  have hKz : ∀ i ∈ Finset.range n, (K i : ℍ → ℂ) z = δ ^ (12 * μ) * (K i : ℍ → ℂ) τ :=
    fun i hi => hK i hi A τ

  set u : ℂ := g z ^ (2 * M) * ModularForm.E₄ z ^ (3 * (m * M) + 3) * ModularForm.E₆ z ^ (2 * (m * M)) with hu
  set v : ℂ := h z ^ (2 * M) * ModularForm.discriminant z ^ (2 * (m * M) + 1) with hv
  have hid : u ^ n * ModularForm.E₄ z ^ (3 * μ) +
      ∑ i ∈ Finset.range n, (K i : ℍ → ℂ) z * (u ^ i * v ^ (n - i)) = 0 := by
    have := congrArg (ANb.ev z) hE
    simp only [map_add, map_sum, map_mul, map_pow, map_zero, ANb.ev_apply] at this
    exact this
  clear_value u v

  rw [ANb.slash_coe_apply, ANb.slash_coe_apply]
  change ‖g z * (ModularForm.E₄ z ^ 2 * ModularForm.E₆ z) ^ m * δ ^ (-(k + 14 * (m : ℤ)))‖ ≤
    ε * ‖h z * ModularForm.discriminant z ^ m * δ ^ (-(k + 12 * (m : ℤ)))‖
  by_cases hv0 : v = 0
  ·
    have hMpos : M ≠ 0 := by
      rintro rfl
      apply hd0
      have : ModularForm.discriminant z ^ (2 * (m * 0) + 1) = 0 := by simpa [hv] using hv0
      rw [mul_zero, mul_zero, zero_add, pow_one] at this
      simpa [hΔz, hδ] using this
    have hsum0 : ∑ i ∈ Finset.range n, (K i : ℍ → ℂ) z * (u ^ i * v ^ (n - i)) = 0 := by
      refine Finset.sum_eq_zero fun i hi => ?_
      have : n - i ≠ 0 := Nat.sub_ne_zero_of_lt (Finset.mem_range.mp hi)
      rw [hv0, zero_pow this, mul_zero, mul_zero]
    rw [hsum0, add_zero] at hid
    have hE4z0 : ModularForm.E₄ z ≠ 0 := by rw [hE4z]; exact mul_ne_zero (pow_ne_zero _ hδ) ha0
    have hE6z0 : ModularForm.E₆ z ≠ 0 := by rw [hE6z]; exact mul_ne_zero (pow_ne_zero _ hδ) hb0
    have hu0 : u = 0 := by
      rcases mul_eq_zero.mp hid with h1 | h1
      · exact pow_eq_zero_iff' |>.mp h1 |>.1
      · exact absurd (pow_eq_zero_iff' |>.mp h1 |>.1) hE4z0
    have hg0 : g z = 0 := by
      simp only [hu, mul_eq_zero, pow_eq_zero_iff', ne_eq] at hu0
      rcases hu0 with (⟨h1, _⟩ | ⟨h1, _⟩) | ⟨h1, _⟩
      · exact h1
      · exact absurd h1 hE4z0
      · exact absurd h1 hE6z0
    rw [hg0, zero_mul, zero_mul, norm_zero]
    exact mul_nonneg hε.le (norm_nonneg _)

  have hE4z0 : ModularForm.E₄ z ≠ 0 := by rw [hE4z]; exact mul_ne_zero (pow_ne_zero _ hδ) ha0

  set U : ℂ := u / v with hU
  have huv : u = U * v := by rw [hU, div_mul_cancel₀ _ hv0]
  let κ : ℕ → ℂ := fun i => (K i : ℍ → ℂ) τ / a ^ (3 * μ)
  have ha3 : a ^ (3 * μ) ≠ 0 := pow_ne_zero _ ha0
  have hE4zm : ModularForm.E₄ z ^ (3 * μ) = δ ^ (12 * μ) * a ^ (3 * μ) := by
    rw [hE4z, mul_pow, ← pow_mul, show 4 * (3 * μ) = 12 * μ by ring]
  have hκ : ∀ i ∈ Finset.range n, (K i : ℍ → ℂ) z = κ i * ModularForm.E₄ z ^ (3 * μ) := by
    intro i hi
    rw [hKz i hi, hE4zm]
    simp only [κ]
    rw [div_mul_eq_mul_div, eq_div_iff ha3]
    ring
  have hrel : U ^ n + ∑ i ∈ Finset.range n, κ i * U ^ i = 0 := by
    have hvn : v ^ n * ModularForm.E₄ z ^ (3 * μ) ≠ 0 := mul_ne_zero (pow_ne_zero _ hv0) (pow_ne_zero _ hE4z0)
    apply (mul_eq_zero.mp ?_).resolve_right hvn
    rw [← hid, add_mul, Finset.sum_mul]
    congr 1
    · rw [huv, mul_pow]; ring
    · refine Finset.sum_congr rfl fun i hi => ?_
      have hin : i ≤ n := (Finset.mem_range.mp hi).le
      rw [hκ i hi, huv, mul_pow, show v ^ n = v ^ i * v ^ (n - i) by rw [← pow_add, Nat.add_sub_cancel' hin]]
      ring
  have h22 : (2 : ℝ) ^ (3 * μ) * (1 / 2) ^ (3 * μ) = 1 := by rw [← mul_pow]; norm_num
  have hκbd : ∀ i ∈ Finset.range n, ‖κ i‖ ≤ B' := by
    intro i hi
    simp only [κ, norm_div, norm_pow]
    have ha3pos : (0 : ℝ) < ‖a‖ ^ (3 * μ) := pow_pos (by linarith) _
    rw [div_le_iff₀ ha3pos]
    have h1 : ‖(K i : ℍ → ℂ) τ‖ ≤ B := (hKτ i hi).trans (hκB i hi)
    have h2 : (1 / 2 : ℝ) ^ (3 * μ) ≤ ‖a‖ ^ (3 * μ) := pow_le_pow_left₀ (by norm_num) ha_lo.le _
    calc ‖(K i : ℍ → ℂ) τ‖ ≤ B := h1
      _ = B * 2 ^ (3 * μ) * (1 / 2 : ℝ) ^ (3 * μ) := by rw [mul_assoc, h22, mul_one]
      _ ≤ B * 2 ^ (3 * μ) * ‖a‖ ^ (3 * μ) :=
          mul_le_mul_of_nonneg_left h2 (mul_nonneg (by linarith) (pow_nonneg (by norm_num) _))
  have hUC : ‖U‖ ≤ C := ANb.norm_le_of_monic_relation hB' hκbd hrel

  set t : ℝ := ‖δ‖ with ht
  have ht0 : 0 < t := norm_pos_iff.mpr hδ
  set ρ : ℝ := ‖δ ^ (-(k + 14 * (m : ℤ)))‖ with hρ
  have hρ0 : 0 < ρ := norm_pos_iff.mpr (zpow_ne_zero _ hδ)
  have hρ1 : ‖δ ^ (-(k + 12 * (m : ℤ)))‖ = ρ * t ^ (2 * m) := by
    rw [show -(k + 12 * (m : ℤ)) = -(k + 14 * (m : ℤ)) + ((2 * m : ℕ) : ℤ) by push_cast; ring, zpow_add₀ hδ, norm_mul,
      ← hρ, zpow_natCast, norm_pow, ← ht]
  set P : ℝ := ‖g z * (ModularForm.E₄ z ^ 2 * ModularForm.E₆ z) ^ m * δ ^ (-(k + 14 * (m : ℤ)))‖ with hP
  set Q : ℝ := ‖h z * ModularForm.discriminant z ^ m * δ ^ (-(k + 12 * (m : ℤ)))‖ with hQ
  have hPe : P = ‖g z‖ * ((t ^ 4 * ‖a‖) ^ 2 * (t ^ 6 * ‖b‖)) ^ m * ρ := by
    rw [hP, norm_mul, norm_mul, ← hρ, norm_pow, norm_mul, norm_pow, hE4z, hE6z, norm_mul, norm_mul, norm_pow, norm_pow]
  have hQe : Q = ‖h z‖ * (t ^ 12 * ‖d‖) ^ m * (ρ * t ^ (2 * m)) := by
    rw [hQ, norm_mul, norm_mul, hρ1, norm_pow, hΔz, norm_mul, norm_pow]
  have hue : ‖u‖ = ‖g z‖ ^ (2 * M) * (t ^ 4 * ‖a‖) ^ (3 * (m * M) + 3) * (t ^ 6 * ‖b‖) ^ (2 * (m * M)) := by
    rw [hu, norm_mul, norm_mul, norm_pow, norm_pow, norm_pow, hE4z, hE6z, norm_mul, norm_mul, norm_pow, norm_pow]
  have hve : ‖v‖ = ‖h z‖ ^ (2 * M) * (t ^ 12 * ‖d‖) ^ (2 * (m * M) + 1) := by
    rw [hv, norm_mul, norm_pow, norm_pow, hΔz, norm_mul, norm_pow]
  have hv' : 0 < ‖v‖ := norm_pos_iff.mpr hv0

  have hT' : P ^ (2 * M) * ‖a‖ ^ (3 * (m * M) + 3) * ‖v‖ = ‖u‖ * Q ^ (2 * M) * ‖d‖ * ‖a‖ ^ (4 * (m * M)) := by
    rw [hPe, hQe, hue, hve]
    ring
  have hT : P ^ (2 * M) * ‖a‖ ^ (3 * (m * M) + 3) = ‖U‖ * Q ^ (2 * M) * ‖d‖ * ‖a‖ ^ (4 * (m * M)) := by
    have hUn : ‖U‖ = ‖u‖ / ‖v‖ := by rw [hU, norm_div]
    rw [hUn, show ‖u‖ / ‖v‖ * Q ^ (2 * M) * ‖d‖ * ‖a‖ ^ (4 * (m * M)) =
      (‖u‖ * Q ^ (2 * M) * ‖d‖ * ‖a‖ ^ (4 * (m * M))) / ‖v‖ by ring, eq_div_iff hv'.ne']
    exact hT'

  have hPnn : 0 ≤ P := norm_nonneg _
  have hQnn : 0 ≤ Q := norm_nonneg _
  by_cases hM : M = 0
  ·
    exfalso
    have hT0 : ‖a‖ ^ 3 = ‖U‖ * ‖d‖ := by simpa [hM] using hT
    have hCη0 : C * η₀ * 2 ^ 3 ≤ 1 := by simpa [hM] using hCη
    have h1 : (1 / 2 : ℝ) ^ 3 < ‖a‖ ^ 3 := pow_lt_pow_left₀ ha_lo (by norm_num) three_ne_zero
    have h2 : ‖U‖ * ‖d‖ ≤ C * η₀ := mul_le_mul hUC hd.le (norm_nonneg _) hC0
    rw [← hT0] at h2
    have h3 : C * η₀ ≤ 1 / 8 := by nlinarith only [hCη0]
    linarith only [h1, h2, h3]
  · have h2M : 2 * M ≠ 0 := by omega
    have hrhs : ‖U‖ * Q ^ (2 * M) * ‖d‖ * ‖a‖ ^ (4 * (m * M)) ≤ C * Q ^ (2 * M) * η₀ * (3 / 2) ^ (4 * (m * M)) := by
      refine mul_le_mul ?_ (pow_le_pow_left₀ (norm_nonneg _) ha_hi.le _)
        (pow_nonneg (norm_nonneg _) _) ?_
      · exact mul_le_mul (mul_le_mul_of_nonneg_right hUC (pow_nonneg hQnn _)) hd.le (norm_nonneg _)
          (mul_nonneg hC0 (pow_nonneg hQnn _))
      · exact mul_nonneg (mul_nonneg hC0 (pow_nonneg hQnn _)) hη₀.le
    have hlhs : P ^ (2 * M) * (1 / 2) ^ (3 * (m * M) + 3) ≤ P ^ (2 * M) * ‖a‖ ^ (3 * (m * M) + 3) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) ha_lo.le _) (pow_nonneg hPnn _)
    have hmain : P ^ (2 * M) * (1 / 2) ^ (3 * (m * M) + 3) ≤ C * Q ^ (2 * M) * η₀ * (3 / 2) ^ (4 * (m * M)) :=
      hlhs.trans (hT ▸ hrhs)
    have h32 : (3 / 2 : ℝ) ^ (4 * (m * M)) ≤ 2 ^ (4 * (m * M)) := pow_le_pow_left₀ (by norm_num) (by norm_num) _
    have hhalf2 : (1 / 2 : ℝ) ^ (3 * (m * M) + 3) * 2 ^ (3 * (m * M) + 3) = 1 := by rw [← mul_pow]; norm_num
    have hcoef : C * η₀ * (3 / 2 : ℝ) ^ (4 * (m * M)) ≤ ε ^ (2 * M) * (1 / 2) ^ (3 * (m * M) + 3) := by
      calc C * η₀ * (3 / 2 : ℝ) ^ (4 * (m * M)) ≤ C * η₀ * 2 ^ (4 * (m * M)) :=
            mul_le_mul_of_nonneg_left h32 (mul_nonneg hC0 hη₀.le)
        _ = C * η₀ * (2 ^ (3 * (m * M) + 3) * 2 ^ (4 * (m * M))) * (1 / 2) ^ (3 * (m * M) + 3) := by
            rw [show C * η₀ * (2 ^ (3 * (m * M) + 3) * 2 ^ (4 * (m * M))) * (1 / 2 : ℝ) ^ (3 * (m * M) + 3) =
              C * η₀ * 2 ^ (4 * (m * M)) * ((1 / 2 : ℝ) ^ (3 * (m * M) + 3) * 2 ^ (3 * (m * M) + 3)) by ring, hhalf2, mul_one]
        _ ≤ ε ^ (2 * M) * (1 / 2) ^ (3 * (m * M) + 3) :=
            mul_le_mul_of_nonneg_right hCη (pow_nonneg (by norm_num) _)
    have hpow : P ^ (2 * M) ≤ (ε * Q) ^ (2 * M) := by
      have hhalf : (0 : ℝ) < (1 / 2) ^ (3 * (m * M) + 3) := pow_pos (by norm_num) _
      have : P ^ (2 * M) * (1 / 2) ^ (3 * (m * M) + 3) ≤ (ε * Q) ^ (2 * M) * (1 / 2) ^ (3 * (m * M) + 3) := by
        calc P ^ (2 * M) * (1 / 2) ^ (3 * (m * M) + 3) ≤ C * Q ^ (2 * M) * η₀ * (3 / 2) ^ (4 * (m * M)) := hmain
          _ = Q ^ (2 * M) * (C * η₀ * (3 / 2) ^ (4 * (m * M))) := by ring
          _ ≤ Q ^ (2 * M) * (ε ^ (2 * M) * (1 / 2) ^ (3 * (m * M) + 3)) :=
              mul_le_mul_of_nonneg_left hcoef (pow_nonneg hQnn _)
          _ = (ε * Q) ^ (2 * M) * (1 / 2) ^ (3 * (m * M) + 3) := by ring
      exact le_of_mul_le_mul_right this hhalf
    exact (pow_le_pow_iff_left₀ hPnn (mul_nonneg hε.le hQnn) h2M).mp hpow
