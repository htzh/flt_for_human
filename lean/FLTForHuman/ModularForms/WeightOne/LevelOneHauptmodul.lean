/-
  The four closure-1 level-one Hauptmodul leaves (SET-6 order 1).

  Each statement is the pinned wrapper `Theorems/Thm_<name>.lean` verbatim; each
  proof is ported from the matching `P2M/Sol/S_<name>.lean`, adapted to mathlib
  `v4.34.0`. The pin's helpers are all `private` here, so the checker sees only
  the four headlines:

  * `ModularCurve.surjective_specialLinearGroup_map_zmod` — reduction
    `SL(2, ℤ) → SL(2, ℤ/N)` is onto (`exists_sl2_int_lift`);
  * `ModularCurve.qExpansion_discriminant_eq_X_mul_tprod` — the `q`-expansion of
    `Δ` as `q ∏ (1 - qⁿ)²⁴` (the truncated-polynomial Taylor argument);
  * `WLight.isZeroAtImInfty_mul_disc_iff_qExpansion_coeff_le` — vanishing at
    cusps is a width-`N` coefficient bound;
  * `WLight.linearIndependent_complex_of_qExpansion_rational` — rational
    `q`-coefficients are a faithful linear invariant.

  The three big Hauptmodul packages (`levelOne_hauptmodul_package`,
  `weierstrassP_qExpansion_package`, `weierstrassP_torsion_qExpansion_package`)
  are SET 7 and are **not** ported here.

  FLT `anthropics/fermats-last-theorem@aa2d8b3`:
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_surjective_specialLinearGroup_map_zmod.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_qExpansion_discriminant_eq_X_mul_tprod.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_WLight_isZeroAtImInfty_mul_disc_iff_qExpansion_coeff_le.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_WLight_linearIndependent_complex_of_qExpansion_rational.lean

  v4.34 drifts hit here: `if_neg` → `ite_eq_right` (the coefficient-stabilisation
  lemma), and `Complex.exp_ne_zero`/`Real.exp_pos` names are unchanged. The
  pin's local `set_option maxHeartbeats 1600000` on the width lemma is **not**
  transcribed: the project's global cap is `4000000`, above it.
-/
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.Data.Int.GCD
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.Geometry.Manifold.Notation
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.CuspFormSubmodule
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
import Mathlib.NumberTheory.ModularForms.LevelOne.Basic
import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.PowerSeries.PiTopology

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

/-! ## 1. `SL(2, ℤ) → SL(2, ℤ/N)` is onto -/

namespace ModularCurve

open Matrix Finset

private lemma natCast_dvd_int {p : ℕ} {z : ℤ} : (p : ℤ) ∣ z ↔ p ∣ z.natAbs :=
  Int.natCast_dvd

private def primeSel (c d : ℤ) : ℕ :=
  ∏ p ∈ c.natAbs.primeFactors, if p ∣ d.natAbs then 1 else p

private lemma dvd_primeSel {c d : ℤ} {p : ℕ} (hc : c ≠ 0) (hp : p.Prime)
    (hpc : (p : ℤ) ∣ c) (hpd : ¬(p : ℤ) ∣ d) : p ∣ primeSel c d := by
  have hmem : p ∈ c.natAbs.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp, natCast_dvd_int.mp hpc, Int.natAbs_ne_zero.mpr hc⟩
  have h := Finset.dvd_prod_of_mem (fun q : ℕ => if q ∣ d.natAbs then 1 else q) hmem
  simp only [ite_eq_right (fun hcontra => hpd (natCast_dvd_int.mpr hcontra))] at h
  exact h

private lemma not_dvd_primeSel {c d : ℤ} {p : ℕ} (hp : p.Prime) (hpd : (p : ℤ) ∣ d) :
    ¬p ∣ primeSel c d := by
  intro hdvd
  obtain ⟨q, hq, hpq⟩ := (Nat.Prime.prime hp).dvd_finsetProd_iff _ |>.mp hdvd
  by_cases hqd : q ∣ d.natAbs
  · rw [ite_eq_left hqd] at hpq
    exact hp.one_lt.ne' (Nat.dvd_one.mp hpq)
  · rw [ite_eq_right hqd] at hpq
    have hq' : q.Prime := (Nat.mem_primeFactors.mp hq).1
    exact hqd (((Nat.prime_dvd_prime_iff_eq hp hq').mp hpq) ▸ natCast_dvd_int.mp hpd)

private theorem exists_coprime_lift (N : ℕ) [NeZero N] {c₀ d₀ : ℤ}
    (H : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ c₀ → (p : ℤ) ∣ d₀ → ¬(p : ℤ) ∣ (N : ℤ)) :
    ∃ γ δ : ℤ, Int.gcd γ δ = 1 ∧
      (γ : ZMod N) = (c₀ : ZMod N) ∧ (δ : ZMod N) = (d₀ : ZMod N) := by
  set γ : ℤ := if c₀ = 0 then (N : ℤ) else c₀ with hγ_def
  have hγ0 : γ ≠ 0 := by
    rw [hγ_def]
    split
    · exact_mod_cast NeZero.ne N
    · assumption
  have hγc : (γ : ZMod N) = (c₀ : ZMod N) := by
    rw [hγ_def]
    split
    · next h => simp [h]
    · rfl
  have Hγ : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ γ → (p : ℤ) ∣ d₀ → ¬(p : ℤ) ∣ (N : ℤ) := by
    intro p pp hpγ hpd
    refine H p pp ?_ hpd
    rw [hγ_def] at hpγ
    by_cases h : c₀ = 0
    · simp [h]
    · rwa [ite_eq_right h] at hpγ
  refine ⟨γ, d₀ + (primeSel γ d₀ : ℤ) * (N : ℤ), ?_, hγc, ?_⟩
  · by_contra hne
    obtain ⟨p, pp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
    have h1 : (p : ℤ) ∣ γ :=
      natCast_dvd_int.mpr (hpdvd.trans (Nat.gcd_dvd_left _ _))
    have h2 : (p : ℤ) ∣ d₀ + (primeSel γ d₀ : ℤ) * (N : ℤ) :=
      natCast_dvd_int.mpr (hpdvd.trans (Nat.gcd_dvd_right _ _))
    by_cases hpd : (p : ℤ) ∣ d₀
    · have h3 : (p : ℤ) ∣ (primeSel γ d₀ : ℤ) * (N : ℤ) := by
        have := h2.sub hpd
        rwa [add_sub_cancel_left] at this
      have h3' : p ∣ primeSel γ d₀ * N := by
        have heq : (primeSel γ d₀ : ℤ) * (N : ℤ) = ((primeSel γ d₀ * N : ℕ) : ℤ) := by
          push_cast; ring
        rw [heq] at h3
        exact natCast_dvd_int.mp h3
      rcases (Nat.Prime.dvd_mul pp).mp h3' with h4 | h4
      · exact not_dvd_primeSel pp hpd h4
      · exact Hγ p pp h1 hpd (natCast_dvd_int.mpr h4)
    · have h3 : (p : ℤ) ∣ (primeSel γ d₀ : ℤ) :=
        natCast_dvd_int.mpr (dvd_primeSel hγ0 pp h1 hpd)
      refine hpd ?_
      have := h2.sub (h3.mul_right (N : ℤ))
      rwa [add_sub_cancel_right] at this
  · push_cast
    simp

private theorem exists_sl2_int_lift {N : ℕ} [NeZero N] {a b c d : ZMod N}
    (h : a * d - b * c = 1) :
    ∃ α β γ δ : ℤ, α * δ - β * γ = 1 ∧
      (α : ZMod N) = a ∧ (β : ZMod N) = b ∧ (γ : ZMod N) = c ∧ (δ : ZMod N) = d := by
  set a₀ : ℤ := ZMod.cast a with ha₀
  set b₀ : ℤ := ZMod.cast b with hb₀
  set c₀ : ℤ := ZMod.cast c with hc₀
  set d₀ : ℤ := ZMod.cast d with hd₀
  have hcasta : ((a₀ : ℤ) : ZMod N) = a := ZMod.intCast_zmod_cast a
  have hcastb : ((b₀ : ℤ) : ZMod N) = b := ZMod.intCast_zmod_cast b
  have hcastc : ((c₀ : ℤ) : ZMod N) = c := ZMod.intCast_zmod_cast c
  have hcastd : ((d₀ : ℤ) : ZMod N) = d := ZMod.intCast_zmod_cast d
  have hdvd : (N : ℤ) ∣ a₀ * d₀ - b₀ * c₀ - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hcasta, hcastb, hcastc, hcastd]
    rw [sub_eq_zero]
    exact h
  have H : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ c₀ → (p : ℤ) ∣ d₀ → ¬(p : ℤ) ∣ (N : ℤ) := by
    intro p pp hpc hpd hpN
    have hone : (p : ℤ) ∣ 1 := by
      have h1 : (p : ℤ) ∣ a₀ * d₀ - b₀ * c₀ - 1 := hpN.trans hdvd
      have h2 : (p : ℤ) ∣ a₀ * d₀ := hpd.mul_left a₀
      have h3 : (p : ℤ) ∣ b₀ * c₀ := hpc.mul_left b₀
      have key : (1 : ℤ) = a₀ * d₀ - b₀ * c₀ - (a₀ * d₀ - b₀ * c₀ - 1) := by ring
      rw [key]
      exact (h2.sub h3).sub h1
    exact pp.one_lt.ne' (Nat.dvd_one.mp (by exact_mod_cast hone))
  obtain ⟨γ, δ, hγδ, hγ, hδ⟩ := exists_coprime_lift N H
  rw [hcastc] at hγ
  rw [hcastd] at hδ
  set α₀ : ℤ := Int.gcdB γ δ with hα₀
  set β₀ : ℤ := -Int.gcdA γ δ with hβ₀
  have hdet₀ : α₀ * δ - β₀ * γ = 1 := by
    have hbez := Int.gcd_eq_gcd_ab γ δ
    rw [hγδ] at hbez
    push_cast at hbez
    rw [hα₀, hβ₀]
    linear_combination -hbez
  have hdet₀' : (α₀ : ZMod N) * d - (β₀ : ZMod N) * c = 1 := by
    have := congrArg (fun z : ℤ => (z : ZMod N)) hdet₀
    push_cast at this
    rwa [hγ, hδ] at this
  set lam : ZMod N := b * (α₀ : ZMod N) - a * (β₀ : ZMod N) with hlam
  set l : ℤ := ZMod.cast lam with hl
  have hcastl : ((l : ℤ) : ZMod N) = lam := ZMod.intCast_zmod_cast lam
  refine ⟨α₀ + l * γ, β₀ + l * δ, γ, δ, ?_, ?_, ?_, hγ, hδ⟩
  · linear_combination hdet₀
  · push_cast
    rw [hcastl, hγ, hlam]
    linear_combination (-(α₀ : ZMod N)) * h + a * hdet₀'
  · push_cast
    rw [hcastl, hδ, hlam]
    linear_combination (-(β₀ : ZMod N)) * h + b * hdet₀'

end ModularCurve

open scoped MatrixGroups

theorem ModularCurve.surjective_specialLinearGroup_map_zmod (N : ℕ) [NeZero N] :
    Function.Surjective
      (Matrix.SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom (ZMod N))) := by
  intro M
  have hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
    have hM := M.prop
    rwa [Matrix.det_fin_two] at hM
  obtain ⟨α, β, γ, δ, h1, ha, hb, hc, hd⟩ := ModularCurve.exists_sl2_int_lift hdet
  refine ⟨⟨!![α, β; γ, δ], by rw [Matrix.det_fin_two_of]; exact h1⟩, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simpa [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
      using ‹_›

/-! ## 2. The discriminant's eta-product `q`-expansion -/

namespace ModularCurve

open UpperHalfPlane Complex Filter Topology
open scoped MatrixGroups PowerSeries.WithPiTopology

local notation "𝕢" => Function.Periodic.qParam

open Polynomial in

private def truncPoly (N : ℕ) : ℂ[X] := ∏ n ∈ Finset.range N, (1 - Polynomial.X ^ (n + 1)) ^ 24

private def etaPow : PowerSeries ℂ := ∏' n : ℕ, (1 - PowerSeries.X ^ (n + 1)) ^ 24

private def gfun (q : ℂ) : ℂ := ∏' n : ℕ, (1 - q ^ (n + 1)) ^ 24

private lemma multipliable_factor_pow :
    Multipliable fun n : ℕ => ((1 : PowerSeries ℂ) - PowerSeries.X ^ (n + 1)) ^ 24 :=
  (PowerSeries.WithPiTopology.multipliable_one_sub_X_pow ℂ).pow 24

private lemma coeff_mul_factor_eq {m n : ℕ} (hmn : m < n + 1) (Q : PowerSeries ℂ) :
    PowerSeries.coeff m (Q * ((1 : PowerSeries ℂ) - PowerSeries.X ^ (n + 1)) ^ 24) =
      PowerSeries.coeff m Q := by

  obtain ⟨R, hR⟩ : PowerSeries.X ^ (n + 1) ∣
      ((1 : PowerSeries ℂ) - PowerSeries.X ^ (n + 1)) ^ 24 - 1 := by
    have h := sub_dvd_pow_sub_pow ((1 : PowerSeries ℂ) - PowerSeries.X ^ (n + 1)) 1 24
    rw [one_pow, sub_sub_cancel_left] at h
    exact neg_dvd.mp h
  replace hR : ((1 : PowerSeries ℂ) - PowerSeries.X ^ (n + 1)) ^ 24 =
      1 + PowerSeries.X ^ (n + 1) * R := by
    rw [← hR]; ring
  rw [hR, mul_add, mul_one, map_add, ← mul_assoc, mul_comm Q, mul_assoc,
    PowerSeries.coeff_X_pow_mul', ite_eq_right (not_le.mpr hmn), add_zero]

private lemma coeff_trunc_eq_coeff_etaPow (m : ℕ) {N : ℕ} (hN : m < N) :
    PowerSeries.coeff m (∏ n ∈ Finset.range N, ((1 : PowerSeries ℂ) - PowerSeries.X ^ (n + 1)) ^ 24) =
      PowerSeries.coeff m etaPow := by

  have hlim : Tendsto (fun N => PowerSeries.coeff m
      (∏ n ∈ Finset.range N, ((1 : PowerSeries ℂ) - PowerSeries.X ^ (n + 1)) ^ 24)) atTop
      (𝓝 (PowerSeries.coeff m etaPow)) :=
    ((PowerSeries.WithPiTopology.continuous_coeff ℂ m).tendsto _).comp
      multipliable_factor_pow.hasProd.tendsto_prod_nat

  have hconst : ∀ N', m < N' → ∀ N, N' ≤ N →
      PowerSeries.coeff m (∏ n ∈ Finset.range N, ((1 : PowerSeries ℂ) - PowerSeries.X ^ (n + 1)) ^ 24) =
      PowerSeries.coeff m (∏ n ∈ Finset.range N', ((1 : PowerSeries ℂ) - PowerSeries.X ^ (n + 1)) ^ 24) := by
    intro N' hN' N hle
    induction N, hle using Nat.le_induction with
    | base => rfl
    | succ N hle ih => rw [Finset.prod_range_succ, coeff_mul_factor_eq (by omega), ih]
  have hev : (fun N => PowerSeries.coeff m
      (∏ n ∈ Finset.range N, ((1 : PowerSeries ℂ) - PowerSeries.X ^ (n + 1)) ^ 24)) =ᶠ[atTop]
      fun _ => PowerSeries.coeff m
        (∏ n ∈ Finset.range N, ((1 : PowerSeries ℂ) - PowerSeries.X ^ (n + 1)) ^ 24) :=
    eventually_atTop.mpr ⟨N, fun N'' h => hconst N hN N'' h⟩
  exact (tendsto_nhds_unique (hlim.congr' hev) tendsto_const_nhds).symm

open Polynomial in
private lemma truncPoly_toPowerSeries (N : ℕ) :
    ((truncPoly N : ℂ[X]) : PowerSeries ℂ) =
      ∏ n ∈ Finset.range N, ((1 : PowerSeries ℂ) - PowerSeries.X ^ (n + 1)) ^ 24 := by
  rw [truncPoly, ← Polynomial.coeToPowerSeries.ringHom_apply, map_prod]
  simp [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_pow, Polynomial.coe_X]

open Polynomial in

private lemma iterate_deriv_polynomial_eval (p : ℂ[X]) (m : ℕ) :
    deriv^[m] (fun q : ℂ => p.eval q) = fun q => (derivative^[m] p).eval q := by
  induction m generalizing p with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ', Function.comp_apply, ih, Function.iterate_succ',
      Function.comp_apply]
    funext q
    exact Polynomial.deriv _

open Polynomial in
private lemma truncPoly_eval (N : ℕ) (q : ℂ) :
    (truncPoly N).eval q = ∏ n ∈ Finset.range N, (1 - q ^ (n + 1)) ^ 24 := by
  simp [truncPoly, Polynomial.eval_prod]

private lemma tendstoLocallyUniformlyOn_trunc :
    TendstoLocallyUniformlyOn (fun N q => ∏ n ∈ Finset.range N, (1 - q ^ (n + 1)) ^ 24) gfun atTop
      (Metric.ball (0 : ℂ) 1) := by
  have h1 : TendstoLocallyUniformlyOn (fun N q => ∏ n ∈ Finset.range N, (1 - q ^ (n + 1)))
      (fun q => ∏' n : ℕ, (1 - q ^ (n + 1))) atTop (Metric.ball (0 : ℂ) 1) := by
    have := ModularForm.multipliableLocallyUniformlyOn_one_sub_pow.hasProdLocallyUniformlyOn
      |>.tendstoLocallyUniformlyOn_finsetRange
    refine this.congr (fun N => ?_)
    intro q _
    simp
  have hc : ContinuousOn (fun q : ℂ => ∏' n : ℕ, (1 - q ^ (n + 1))) (Metric.ball (0 : ℂ) 1) :=
    ModularForm.differentiableOn_tprod_one_sub_pow.continuousOn

  have hpow : ∀ k : ℕ, TendstoLocallyUniformlyOn
      (fun N q => (∏ n ∈ Finset.range N, (1 - q ^ (n + 1))) ^ k)
      (fun q => (∏' n : ℕ, (1 - q ^ (n + 1))) ^ k) atTop (Metric.ball (0 : ℂ) 1) := by
    intro k
    induction k with
    | zero =>
      simp only [pow_zero]
      intro u hu x _
      exact ⟨Set.univ, Filter.univ_mem, Eventually.of_forall fun n y _ => refl_mem_uniformity hu⟩
    | succ k ih =>
      simp only [pow_succ]
      exact ih.mul₀ h1 (hc.pow k) hc
  refine ((hpow 24).congr fun N q _ => ?_).congr_right fun q hq => ?_
  · exact (Finset.prod_pow _ _ _).symm
  · exact ((ModularForm.multipliable_one_sub_pow (by simpa using hq)).tprod_pow 24).symm

private lemma differentiableOn_gfun : DifferentiableOn ℂ gfun (Metric.ball (0 : ℂ) 1) :=
  ModularForm.differentiableOn_tprod_one_sub_pow_pow 24

open Polynomial in

private lemma tendstoLocallyUniformlyOn_iterate_deriv_trunc (m : ℕ) :
    TendstoLocallyUniformlyOn (fun N q => (derivative^[m] (truncPoly N)).eval q) (deriv^[m] gfun)
      atTop (Metric.ball (0 : ℂ) 1) := by
  induction m with
  | zero =>
    simpa only [Function.iterate_zero, id_eq, truncPoly_eval] using tendstoLocallyUniformlyOn_trunc
  | succ m ih =>
    have h := ih.deriv (Eventually.of_forall fun N => (Polynomial.differentiable _).differentiableOn)
      Metric.isOpen_ball
    rw [Function.iterate_succ', Function.iterate_succ']
    refine h.congr fun N q _ => ?_
    simp only [Function.comp_apply, Polynomial.deriv]

open Polynomial in

private lemma iteratedDeriv_gfun_zero (m : ℕ) :
    iteratedDeriv m gfun 0 = m.factorial * PowerSeries.coeff m etaPow := by
  have h0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := Metric.mem_ball_self one_pos
  have hlim : Tendsto (fun N => (derivative^[m] (truncPoly N)).eval 0) atTop
      (𝓝 (deriv^[m] gfun 0)) :=
    (tendstoLocallyUniformlyOn_iterate_deriv_trunc m).tendsto_at h0

  have hev : (fun N => (derivative^[m] (truncPoly N)).eval 0) =ᶠ[atTop]
      fun _ => (m.factorial : ℂ) * PowerSeries.coeff m etaPow := by
    refine eventually_atTop.mpr ⟨m + 1, fun N hN => ?_⟩
    simp only
    rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_iterate_derivative, zero_add,
      Nat.descFactorial_self, nsmul_eq_mul, ← Polynomial.coeff_coe, truncPoly_toPowerSeries,
      coeff_trunc_eq_coeff_etaPow m (by omega)]
  rw [iteratedDeriv_eq_iterate]
  exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' hev.symm)

private lemma hasSum_coeff_etaPow {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun m : ℕ => PowerSeries.coeff m etaPow * q ^ m) (gfun q) := by
  have hq' : q ∈ Metric.ball (0 : ℂ) 1 := by simpa using hq
  have h := Complex.hasSum_taylorSeries_on_ball differentiableOn_gfun hq'
  refine h.congr_fun fun m => ?_
  rw [iteratedDeriv_gfun_zero, sub_zero, smul_eq_mul, smul_eq_mul]
  field_simp
  rw [mul_div_assoc, div_self (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)), mul_one]

private lemma hasSum_coeff_X_mul_etaPow {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun m : ℕ => PowerSeries.coeff m (PowerSeries.X * etaPow) * q ^ m) (q * gfun q) := by
  have h := (hasSum_coeff_etaPow hq).mul_left q
  rw [← hasSum_nat_add_iff' 1]
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, mul_one, PowerSeries.coeff_zero_X_mul,
    sub_zero]
  refine h.congr_fun fun m => ?_
  rw [PowerSeries.coeff_succ_X_mul, pow_succ]
  ring

private lemma discriminant_eq_qParam_mul_gfun (τ : ℍ) :
    ModularForm.discriminant τ = 𝕢 1 (τ : ℂ) * gfun (𝕢 1 (τ : ℂ)) := by

  rw [ModularForm.discriminant_eq_q_prod, gfun]

theorem qExpansion_discriminant_eq_X_mul_tprod :
    UpperHalfPlane.qExpansion 1 ModularForm.discriminant =
      PowerSeries.X * ∏' n : ℕ, ((1 : PowerSeries ℂ) - PowerSeries.X ^ (n + 1)) ^ 24 := by
  have hsum : ∀ τ : ℍ, HasSum (fun m : ℕ =>
      PowerSeries.coeff m (PowerSeries.X * etaPow) • 𝕢 1 (τ : ℂ) ^ m) (CuspForm.discriminant τ) := by
    intro τ
    simp_rw [smul_eq_mul, CuspForm.coe_discriminant, discriminant_eq_qParam_mul_gfun τ]
    exact hasSum_coeff_X_mul_etaPow (by exact_mod_cast UpperHalfPlane.norm_qParam_lt_one 1 τ)
  ext m
  have h := ModularFormClass.qExpansion_coeff_unique one_pos
    one_mem_strictPeriods_SL (f := CuspForm.discriminant) hsum m
  rw [CuspForm.coe_discriminant] at h
  rw [← h]
  rfl

end ModularCurve

/-! ## 3. Vanishing at cusps as a width-`N` coefficient bound -/

namespace WLight

open Complex Real UpperHalfPlane Function Filter Polynomial Asymptotics
open scoped Topology Manifold MatrixGroups ModularForm

section Division

private theorem powerSeries_coeff_mem_of_mul_eq {K : Type*} [Field K] (k : Subfield K)
    {g h f : PowerSeries K} (heq : g * h = f) (hg0 : PowerSeries.constantCoeff g ≠ 0)
    (hg : ∀ n, PowerSeries.coeff n g ∈ k) (hf : ∀ n, PowerSeries.coeff n f ∈ k) :
    ∀ n, PowerSeries.coeff n h ∈ k := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  have hcm := PowerSeries.coeff_mul n g h
  rw [heq] at hcm
  have h0n : (0, n) ∈ Finset.HasAntidiagonal.antidiagonal n := Finset.HasAntidiagonal.mem_antidiagonal.mpr (zero_add n)
  rw [← Finset.add_sum_erase _ _ h0n] at hcm
  have hg0' : PowerSeries.coeff 0 g ≠ 0 := by
    rwa [PowerSeries.coeff_zero_eq_constantCoeff_apply]
  have hrest : (∑ p ∈ (Finset.HasAntidiagonal.antidiagonal n).erase (0, n),
      PowerSeries.coeff p.1 g * PowerSeries.coeff p.2 h) ∈ k := by
    refine sum_mem fun p hp ↦ mul_mem (hg p.1) (ih p.2 ?_)
    obtain ⟨hpne, hpmem⟩ := Finset.mem_erase.mp hp
    have hpsum : p.1 + p.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hpmem
    rcases p with ⟨p1, p2⟩
    simp only [Prod.mk.injEq, not_and, ne_eq] at hpne
    dsimp only at hpsum
    omega
  have hn : PowerSeries.coeff n h = (PowerSeries.coeff 0 g)⁻¹ *
      (PowerSeries.coeff n f - ∑ p ∈ (Finset.HasAntidiagonal.antidiagonal n).erase (0, n),
        PowerSeries.coeff p.1 g * PowerSeries.coeff p.2 h) := by
    rw [eq_inv_mul_iff_mul_eq₀ hg0', eq_sub_iff_add_eq]
    exact hcm.symm
  rw [hn]
  exact mul_mem (inv_mem (hg 0)) (sub_mem (hf n) hrest)

private theorem powerSeries_coeff_mem_of_mul_eq' {K : Type*} [Field K] (k : Subfield K)
    {g h f : PowerSeries K} (heq : g * h = f) (hg0 : g ≠ 0)
    (hg : ∀ n, PowerSeries.coeff n g ∈ k) (hf : ∀ n, PowerSeries.coeff n f ∈ k) :
    ∀ n, PowerSeries.coeff n h ∈ k := by
  set r := (PowerSeries.order g).toNat with hr_def
  obtain ⟨g', hg'⟩ : (PowerSeries.X : PowerSeries K) ^ r ∣ g := PowerSeries.X_pow_dvd_iff.mpr
    (fun m hm ↦ PowerSeries.coeff_of_lt_order_toNat (φ := g) m hm)
  have hg'_coeff : ∀ n, PowerSeries.coeff n g' ∈ k := fun n ↦ by
    have h1 := hg (n + r)
    rwa [hg', PowerSeries.coeff_X_pow_mul g' r n] at h1
  have hg'_cc : PowerSeries.constantCoeff g' ≠ 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    intro habs
    refine (PowerSeries.coeff_order hg0) ?_
    show PowerSeries.coeff r g = 0
    rw [hg', PowerSeries.coeff_X_pow_mul', ite_eq_left le_rfl, Nat.sub_self, habs]
  obtain ⟨f', hf'⟩ : PowerSeries.X ^ r ∣ f := ⟨g' * h, by rw [← heq, hg', mul_assoc]⟩
  have hf'_coeff : ∀ n, PowerSeries.coeff n f' ∈ k := fun n ↦ by
    have h1 := hf (n + r); rwa [hf', PowerSeries.coeff_X_pow_mul f' r n] at h1
  have heq' : g' * h = f' := by
    have hX : (PowerSeries.X : PowerSeries K) ^ r ≠ 0 := pow_ne_zero _ PowerSeries.X_ne_zero
    have h2 := hf' ▸ hg' ▸ heq
    rw [mul_assoc] at h2
    exact mul_left_cancel₀ hX h2
  exact powerSeries_coeff_mem_of_mul_eq k heq' hg'_cc hg'_coeff hf'_coeff

private theorem norm_le_of_monicRel {K : Type*} [NormedField K] {z : K} {a : ℕ → K} {d : ℕ}
    (h : z ^ d + ∑ n ∈ Finset.range d, a n * z ^ n = 0) :
    ‖z‖ ≤ 1 + ∑ n ∈ Finset.range d, ‖a n‖ := by
  have hsum : ‖z‖ ^ d ≤ ∑ n ∈ Finset.range d, ‖a n‖ * ‖z‖ ^ n := by
    calc ‖z‖ ^ d = ‖z ^ d‖ := (norm_pow _ _).symm
      _ = ‖-∑ n ∈ Finset.range d, a n * z ^ n‖ :=
          congrArg _ (eq_neg_of_add_eq_zero_left h)
      _ = ‖∑ n ∈ Finset.range d, a n * z ^ n‖ := norm_neg _
      _ ≤ ∑ n ∈ Finset.range d, ‖a n * z ^ n‖ := norm_sum_le _ _
      _ = ∑ n ∈ Finset.range d, ‖a n‖ * ‖z‖ ^ n :=
          Finset.sum_congr rfl fun n _ ↦ by rw [norm_mul, norm_pow]
  rcases le_or_gt ‖z‖ 1 with h1 | h1
  · exact h1.trans (le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _))
  · have hzpos : 0 < ‖z‖ := lt_of_lt_of_le one_pos h1.le
    have hd : 0 < d := by
      by_contra hd0
      simp only [Nat.eq_zero_of_not_pos hd0, pow_zero, Finset.range_zero,
        Finset.sum_empty] at hsum
      exact absurd hsum (not_le.mpr one_pos)
    have hpow : ∀ n ∈ Finset.range d, ‖z‖ ^ n ≤ ‖z‖ ^ (d - 1) := fun n hn ↦
      pow_le_pow_right₀ h1.le (Nat.le_sub_one_of_lt (Finset.mem_range.mp hn))
    have : ‖z‖ ^ d ≤ (∑ n ∈ Finset.range d, ‖a n‖) * ‖z‖ ^ (d - 1) := by
      calc ‖z‖ ^ d ≤ ∑ n ∈ Finset.range d, ‖a n‖ * ‖z‖ ^ n := hsum
        _ ≤ ∑ n ∈ Finset.range d, ‖a n‖ * ‖z‖ ^ (d - 1) :=
            Finset.sum_le_sum fun n hn ↦ mul_le_mul_of_nonneg_left (hpow n hn) (norm_nonneg _)
        _ = (∑ n ∈ Finset.range d, ‖a n‖) * ‖z‖ ^ (d - 1) := (Finset.sum_mul ..).symm
    have hzd : ‖z‖ ^ d = ‖z‖ * ‖z‖ ^ (d - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel hd]
    rw [hzd] at this
    have := le_of_mul_le_mul_right (a := ‖z‖ ^ (d - 1)) this (pow_pos hzpos _)
    linarith

private theorem isBoundedAtImInfty_of_monicRel {H : ℍ → ℂ} {c : ℕ → ℍ → ℂ} {d : ℕ}
    (hc : ∀ n < d, IsBoundedAtImInfty (c n))
    (hrel : ∀ τ : ℍ, H τ ^ d + ∑ n ∈ Finset.range d, c n τ * H τ ^ n = 0) :
    IsBoundedAtImInfty H := by
  classical
  choose! C hC using fun n (hn : n < d) ↦ isBigO_iff.mp (hc n hn)
  simp only [Pi.one_apply, norm_one, mul_one] at hC
  have hCev : ∀ᶠ τ in atImInfty, ∀ n ∈ Finset.range d, ‖c n τ‖ ≤ C n :=
    eventually_all_finset (Finset.range d) |>.mpr fun n hn ↦ hC n (Finset.mem_range.mp hn)
  refine IsBigO.of_bound (1 + ∑ n ∈ Finset.range d, C n) (hCev.mono fun τ hτ ↦ ?_)
  rw [Pi.one_apply, norm_one, mul_one]
  calc ‖H τ‖ ≤ 1 + ∑ n ∈ Finset.range d, ‖c n τ‖ :=
        norm_le_of_monicRel (a := fun n ↦ c n τ) (hrel τ)
    _ ≤ 1 + ∑ n ∈ Finset.range d, C n := by gcongr with n hn; exact hτ n hn

end Division

section CuspCriterion

variable {N : ℕ}

private lemma isBoundedAtImInfty_discriminant : IsBoundedAtImInfty (⇑CuspForm.discriminant : ℍ → ℂ) :=
  (CuspFormClass.zero_at_infty CuspForm.discriminant).boundedAtFilter

private lemma isBoundedAtImInfty_discPow (n : ℕ) :
    IsBoundedAtImInfty (⇑CuspForm.discriminant ^ n : ℍ → ℂ) := by
  induction n with
  | zero => exact pow_zero (⇑CuspForm.discriminant : ℍ → ℂ) ▸ Filter.const_boundedAtFilter _ (1 : ℂ)
  | succ k ih =>
    rw [pow_succ]
    exact ih.mul isBoundedAtImInfty_discriminant

private lemma IsBoundedAtImInfty.mul_discPow_mono {f : ℍ → ℂ} {m m' : ℕ} (hm : m ≤ m')
    (h : IsBoundedAtImInfty (f * ⇑CuspForm.discriminant ^ m)) :
    IsBoundedAtImInfty (f * ⇑CuspForm.discriminant ^ m') := by
  have hshape : (f * ⇑CuspForm.discriminant ^ m' : ℍ → ℂ) =
      (f * ⇑CuspForm.discriminant ^ m) * ⇑CuspForm.discriminant ^ (m' - m) := by
    funext τ
    simp only [Pi.mul_apply, Pi.pow_apply]
    rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' hm]
  rw [hshape]
  exact h.mul (isBoundedAtImInfty_discPow (m' - m))

private def discPowForm (m : ℕ) : ModularForm 𝒮ℒ (12 * m) :=
  ModularForm.mcast (by ring) ((CuspForm.toModularFormₗ CuspForm.discriminant).pow m)

private lemma discPowForm_coe (m : ℕ) : ⇑(discPowForm m) = ⇑CuspForm.discriminant ^ m := by
  funext z
  simp [discPowForm, ModularForm.coe_mcast, ModularForm.coe_pow,
    CuspForm.toModularFormₗ_apply]

private lemma periodic_one_fn (c : ℝ) : Function.Periodic ((1 : ℍ → ℂ) ∘ ofComplex) c := fun _ => rfl

private lemma periodic_discPow_comp_ofComplex (k : ℕ) (N : ℕ) :
    Function.Periodic ((⇑CuspForm.discriminant ^ k : ℍ → ℂ) ∘ ofComplex) N := by
  have h1 : Function.Periodic (⇑CuspForm.discriminant ∘ ofComplex) 1 :=
    SlashInvariantFormClass.periodic_comp_ofComplex CuspForm.discriminant
      one_mem_strictPeriods_SL
  have hk : Function.Periodic ((⇑CuspForm.discriminant ^ k : ℍ → ℂ) ∘ ofComplex) 1 := by
    induction k with
    | zero => exact periodic_one_fn 1
    | succ k ih =>
      intro x
      have hx := (ih.mul h1) x
      simp only [Function.comp_apply, Pi.mul_apply, Pi.pow_apply] at hx ⊢
      rw [pow_succ, pow_succ]
      exact hx
  simpa using hk.nat_mul N

private lemma mdiff_discPow (k : ℕ) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (⇑CuspForm.discriminant ^ k : ℍ → ℂ) := by
  rw [← discPowForm_coe]
  exact (discPowForm k).holo'

private lemma mdiff_mul_discPow {f : ℍ → ℂ} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (m : ℕ) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (f * ⇑CuspForm.discriminant ^ m : ℍ → ℂ) :=
  hf.mul (mdiff_discPow m)

private lemma analyticAt_cuspFunction_zero_of [NeZero N] {g : ℍ → ℂ}
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g)
    (hper : Function.Periodic (g ∘ ofComplex) N) (hbd : IsBoundedAtImInfty g) :
    AnalyticAt ℂ (cuspFunction N g) 0 :=
  analyticAt_cuspFunction_zero
    (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)) hper hhol hbd

private lemma qExpansion_one_discPowForm (k : ℕ) :
    qExpansion 1 (discPowForm k) = (qExpansion 1 ModularForm.discriminant) ^ k := by
  rw [discPowForm, ModularForm.qExpansion_mcast,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]
  have hco : (⇑(CuspForm.toModularFormₗ CuspForm.discriminant) : ℍ → ℂ) =
      ModularForm.discriminant := by
    funext z
    rw [CuspForm.toModularFormₗ_apply]
    exact congrFun CuspForm.coe_discriminant z
  rw [hco]

private lemma qExpansion_one_discPow (k : ℕ) :
    qExpansion 1 (⇑CuspForm.discriminant ^ k : ℍ → ℂ) =
      (qExpansion 1 ModularForm.discriminant) ^ k := by
  rw [← discPowForm_coe]
  exact qExpansion_one_discPowForm k

private lemma coeff_pow_eq_zero_of_lt {D : PowerSeries ℂ} (hD0 : D.coeff 0 = 0) {k n : ℕ}
    (hn : n < k) : (D ^ k).coeff n = 0 := by
  have hX : (PowerSeries.X : PowerSeries ℂ) ∣ D :=
    PowerSeries.X_dvd_iff.mpr (by rwa [← PowerSeries.coeff_zero_eq_constantCoeff])
  exact PowerSeries.X_pow_dvd_iff.mp (pow_dvd_pow_of_dvd hX k) n hn

private lemma discriminant_qExpansion_coeff_zero :
    (qExpansion 1 ModularForm.discriminant).coeff 0 = 0 :=
  CuspFormClass.qExpansion_coeff_zero CuspForm.discriminant one_pos
    one_mem_strictPeriods_SL

private lemma qParam_one_eq_pow {N : ℕ} (hN : N ≠ 0) (τ : ℂ) :
    Function.Periodic.qParam 1 τ = Function.Periodic.qParam N τ ^ N := by
  have : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  simp only [Function.Periodic.qParam, Complex.ofReal_one, div_one, Complex.ofReal_natCast]
  rw [← Complex.exp_nat_mul]
  congr 1
  field_simp

private theorem qExpansion_coeff_width (f : ℍ → ℂ) {N : ℕ} (hN : N ≠ 0)
    (hper : Function.Periodic (f ∘ ofComplex) 1) (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hbd : IsBoundedAtImInfty f) (n : ℕ) :
    (qExpansion N f).coeff n =
      if N ∣ n then (qExpansion 1 f).coeff (n / N) else 0 := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hperN : Function.Periodic (f ∘ ofComplex) N := by
    simpa using hper.nat_mul N
  let f' : C(ℍ, ℂ) := ⟨f, hhol.continuous⟩
  have hfan : AnalyticAt ℂ (cuspFunction N f') 0 :=
    analyticAt_cuspFunction_zero hN' hperN hhol hbd
  set c : ℕ → ℂ := fun n ↦ if N ∣ n then (qExpansion 1 f).coeff (n / N) else 0 with hc
  have hf : ∀ τ : ℍ, HasSum (fun m ↦ c m • Function.Periodic.qParam N τ ^ m) (f' τ) := by
    intro τ
    have h1 := hasSum_qExpansion one_pos hper hhol hbd τ
    have hinj : Function.Injective fun m : ℕ ↦ N * m := fun a b h ↦ by
      simpa [Nat.mul_right_inj hN] using h
    refine (hinj.hasSum_iff (f := fun m ↦ c m • Function.Periodic.qParam N τ ^ m) ?_).mp ?_
    · intro x hx
      have : ¬ N ∣ x := fun ⟨k, hk⟩ ↦ hx ⟨k, hk.symm⟩
      simp [hc, this]
    · refine h1.congr_fun fun m ↦ ?_
      simp only [Function.comp_apply, hc, Nat.dvd_mul_right, ite_true,
        Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hN), qParam_one_eq_pow hN, ← pow_mul]
  exact (qExpansion_coeff_unique f' hN' hfan hf n).symm

private theorem isZeroAtImInfty_iff_qExpansion_coeff_zero_eq_zero {h : ℝ} (hh : 0 < h) {f : ℍ → ℂ}
    (hfper : Periodic (f ∘ ofComplex) h) (hfhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hfbdd : IsBoundedAtImInfty f) :
    IsZeroAtImInfty f ↔ (qExpansion h f).coeff 0 = 0 := by
  have hanal := analyticAt_cuspFunction_zero hh hfper hfhol hfbdd
  rw [qExpansion_coeff_zero hh hanal hfper]
  refine ⟨fun hf ↦ hf.valueAtInfty_eq_zero, fun hv ↦ ?_⟩
  rw [IsZeroAtImInfty, ZeroAtFilter, ← hv, ← cuspFunction_apply_zero hh hanal hfper]
  exact (hanal.continuousAt.tendsto.comp (qParam_tendsto_atImInfty hh)).congr
    (fun τ ↦ eq_cuspFunction τ hh.ne' hfper)

private theorem isBigO_qParam_pow_of_qExpansion_coeff_eq_zero {h : ℝ} (hh : 0 < h) {f : ℍ → ℂ}
    (hfper : Periodic (f ∘ ofComplex) h) (hfhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hfbdd : IsBoundedAtImInfty f)
    {k : ℕ} (hcoeff : ∀ n ≤ k, (qExpansion h f).coeff n = 0) :
    f =O[atImInfty] fun τ ↦ (Periodic.qParam h τ) ^ (k + 1) := by
  have hanal := analyticAt_cuspFunction_zero hh hfper hfhol hfbdd
  have hideriv : ∀ i < k + 1, iteratedDeriv i (cuspFunction h f) 0 = 0 := by
    intro i hi
    have hci := hcoeff i (Nat.lt_succ_iff.mp hi)
    rw [qExpansion_coeff] at hci
    have hfac : ((i.factorial : ℂ))⁻¹ ≠ 0 :=
      inv_ne_zero (Nat.cast_ne_zero.mpr i.factorial_ne_zero)
    exact (mul_eq_zero.mp hci).resolve_left hfac
  have hord : ((k + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt (cuspFunction h f) 0 :=
    (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hanal).mpr hideriv
  obtain ⟨g, hgan, hfac⟩ := (natCast_le_analyticOrderAt hanal).mp hord
  have hOcf : (cuspFunction h f) =O[𝓝 0] fun q : ℂ ↦ q ^ (k + 1) := by
    have hg1 : g =O[𝓝 (0 : ℂ)] (fun _ : ℂ ↦ (1 : ℂ)) := hgan.continuousAt.isBigO_one ℂ
    refine ((isBigO_refl (fun q : ℂ ↦ q ^ (k + 1)) (𝓝 0)).mul hg1).congr' ?_
      (.of_forall fun q ↦ mul_one _)
    filter_upwards [hfac] with q hq
    rw [hq, sub_zero, smul_eq_mul]
  refine (hOcf.comp_tendsto (qParam_tendsto_atImInfty hh)).congr' ?_ (.of_forall fun τ ↦ rfl)
  exact .of_forall fun τ ↦ eq_cuspFunction τ hh.ne' hfper

open ModularForm in

private theorem qParam_pow_isBigO_discPow {N : ℕ} (hN : N ≠ 0) (k : ℕ) :
    (fun τ : ℍ ↦ (Periodic.qParam (N : ℝ) (τ : ℂ)) ^ (N * k)) =O[atImInfty]
      (fun τ ↦ (ModularForm.discriminant τ : ℂ) ^ k) := by
  refine .trans (IsBigO.of_bound 1 (.of_forall fun τ ↦ le_of_eq ?_)) (exp_isBigO_discriminant.pow k)
  rw [one_mul, norm_pow, norm_pow, Real.norm_of_nonneg (Real.exp_pos _).le,
    pow_mul, Function.Periodic.norm_qParam, ← Real.exp_nat_mul, UpperHalfPlane.coe_im]
  congr 2
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  field_simp

open ModularForm in

private theorem isZeroAtImInfty_mul_disc_of_coeff_le {N : ℕ} (hN : N ≠ 0) {F : ℍ → ℂ} {M : ℕ}
    (hM : 1 ≤ M)
    (hfhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (F * ⇑CuspForm.discriminant ^ M))
    (hfper : Periodic ((F * ⇑CuspForm.discriminant ^ M) ∘ ofComplex) N)
    (hfbd : IsBoundedAtImInfty (F * ⇑CuspForm.discriminant ^ M))
    (hcoeff : ∀ n ≤ N * (M - 1), (qExpansion N (F * ⇑CuspForm.discriminant ^ M)).coeff n = 0) :
    IsZeroAtImInfty (F * ⇑CuspForm.discriminant) := by
  set G : ℍ → ℂ := F * ⇑CuspForm.discriminant ^ M with hGdef
  have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hGO : G =O[atImInfty]
      fun τ ↦ (Periodic.qParam (N : ℝ) (τ : ℂ)) ^ (N * (M - 1) + 1) :=
    isBigO_qParam_pow_of_qExpansion_coeff_eq_zero hN' hfper hfhol hfbd hcoeff
  have hqO : (fun τ : ℍ ↦ (Periodic.qParam (N : ℝ) (τ : ℂ)) ^ (N * (M - 1) + 1))
      =O[atImInfty]
        (fun τ ↦ (ModularForm.discriminant τ : ℂ) ^ (M - 1) *
          Periodic.qParam (N : ℝ) (τ : ℂ)) :=
    ((qParam_pow_isBigO_discPow hN (M - 1)).mul
        (isBigO_refl (fun τ : ℍ ↦ Periodic.qParam (N : ℝ) (τ : ℂ)) atImInfty)).congr_left
      (fun τ ↦ (pow_succ _ _).symm)
  have hGO' : G =O[atImInfty]
      (fun τ ↦ (ModularForm.discriminant τ : ℂ) ^ (M - 1) *
        Periodic.qParam (N : ℝ) (τ : ℂ)) := hGO.trans hqO
  have hfdeq : ∀ τ : ℍ, (F * ⇑CuspForm.discriminant) τ
      = G τ / (ModularForm.discriminant τ) ^ (M - 1) := fun τ ↦ by
    have hΔ := ModularForm.discriminant_ne_zero τ
    simp only [hGdef, Pi.mul_apply, Pi.pow_apply, CuspForm.coe_discriminant]
    rw [eq_div_iff (pow_ne_zero _ hΔ), mul_assoc, ← pow_succ', Nat.sub_add_cancel hM]
  have hfneq : (fun τ : ℍ ↦ ‖G τ / ((ModularForm.discriminant τ : ℂ) ^ (M - 1) *
        Periodic.qParam (N : ℝ) (τ : ℂ))‖)
      = (fun τ ↦ ‖(F * ⇑CuspForm.discriminant) τ / Periodic.qParam (N : ℝ) (τ : ℂ)‖) :=
    funext fun τ ↦ by rw [hfdeq, div_div]
  have hbnd : IsBoundedUnder (· ≤ ·) atImInfty
      (fun τ : ℍ ↦ ‖(F * ⇑CuspForm.discriminant) τ / Periodic.qParam (N : ℝ) (τ : ℂ)‖) :=
    hfneq ▸ div_isBoundedUnder_of_isBigO hGO'
  have hq_ne : ∀ τ : ℍ, Periodic.qParam (N : ℝ) (τ : ℂ) ≠ 0 := fun τ ↦
    Complex.exp_ne_zero _
  have hFDO : (F * ⇑CuspForm.discriminant) =O[atImInfty]
      (fun τ : ℍ ↦ Periodic.qParam (N : ℝ) (τ : ℂ)) :=
    (isBigO_iff_div_isBoundedUnder (.of_forall fun τ h ↦ absurd h (hq_ne τ))).mpr hbnd
  exact hFDO.trans_tendsto (qParam_tendsto_atImInfty hN')

open ModularForm in

private lemma qExpansion_discPow_coeff_eq_zero_of_lt [NeZero N] (k : ℕ) {j : ℕ} (hj : j < N * k) :
    (qExpansion N (⇑CuspForm.discriminant ^ k : ℍ → ℂ)).coeff j = 0 := by
  have hper : Function.Periodic
      ((⇑CuspForm.discriminant ^ k : ℍ → ℂ) ∘ ofComplex) (1 : ℂ) := by
    have h := periodic_discPow_comp_ofComplex k 1
    simpa only [Nat.cast_one] using h
  rw [qExpansion_coeff_width _ (NeZero.ne N) hper
    (mdiff_discPow k) (isBoundedAtImInfty_discPow k), qExpansion_one_discPow]
  split_ifs with hN
  · exact coeff_pow_eq_zero_of_lt discriminant_qExpansion_coeff_zero
      (Nat.div_lt_of_lt_mul (Nat.mul_comm N k ▸ hj))
  · rfl

open ModularForm in

private theorem qExpansion_coeff_eq_zero_of_isZeroAtImInfty_mul_disc [NeZero N] {F : ℍ → ℂ} {M : ℕ}
    (hM : 1 ≤ M) (hFhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F)
    (hFper : Function.Periodic (F ∘ ofComplex) N)
    (hz : IsZeroAtImInfty (F * ⇑CuspForm.discriminant)) :
    ∀ n ≤ N * (M - 1), (qExpansion N (F * ⇑CuspForm.discriminant ^ M)).coeff n = 0 := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hFDhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (F * ⇑CuspForm.discriminant) := by
    have := mdiff_mul_discPow hFhol 1; rwa [pow_one] at this
  have hFDper : Function.Periodic ((F * ⇑CuspForm.discriminant) ∘ ofComplex) N := by
    have := hFper.mul (periodic_discPow_comp_ofComplex 1 N); rwa [pow_one] at this
  have hFDbd : IsBoundedAtImInfty (F * ⇑CuspForm.discriminant) := hz.isBoundedAtImInfty
  have hc0 : (qExpansion N (F * ⇑CuspForm.discriminant)).coeff 0 = 0 :=
    (isZeroAtImInfty_iff_qExpansion_coeff_zero_eq_zero hN' hFDper hFDhol hFDbd).mp hz
  have hshape : (F * ⇑CuspForm.discriminant ^ M : ℍ → ℂ)
      = (F * ⇑CuspForm.discriminant) * ⇑CuspForm.discriminant ^ (M - 1) := by
    rw [mul_assoc, ← pow_succ', Nat.sub_add_cancel hM]
  intro n hn
  rw [hshape, qExpansion_mul (analyticAt_cuspFunction_zero_of hFDhol hFDper hFDbd)
      (analyticAt_cuspFunction_zero_of (mdiff_discPow (M - 1))
        (periodic_discPow_comp_ofComplex (M - 1) N) (isBoundedAtImInfty_discPow (M - 1))),
    PowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun ⟨i, j⟩ hij ↦ ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
  rcases lt_or_eq_of_le (show j ≤ N * (M - 1) by omega) with hlt | heq
  · rw [qExpansion_discPow_coeff_eq_zero_of_lt (M - 1) hlt, mul_zero]
  · have : i = 0 := by omega
    rw [this, hc0, zero_mul]

end CuspCriterion

theorem isZeroAtImInfty_mul_disc_iff_qExpansion_coeff_le (N : ℕ) [NeZero N] {F : ℍ → ℂ} {M : ℕ}
    (hM : 1 ≤ M) (hFhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F)
    (hFper : Function.Periodic (F ∘ UpperHalfPlane.ofComplex) N)
    (hFbd : IsBoundedAtImInfty (F * ModularForm.discriminant ^ M)) :
    IsZeroAtImInfty (F * ModularForm.discriminant) ↔
      ∀ n ≤ N * (M - 1),
        (UpperHalfPlane.qExpansion N (F * ModularForm.discriminant ^ M)).coeff n = 0 := by
  rw [show (ModularForm.discriminant : ℍ → ℂ) = ⇑CuspForm.discriminant from
    CuspForm.coe_discriminant.symm]
  have hFbd' : IsBoundedAtImInfty (F * ⇑CuspForm.discriminant ^ M) := by
    rwa [show (⇑CuspForm.discriminant : ℍ → ℂ) = ModularForm.discriminant from
      CuspForm.coe_discriminant]
  exact ⟨qExpansion_coeff_eq_zero_of_isZeroAtImInfty_mul_disc hM hFhol hFper,
    isZeroAtImInfty_mul_disc_of_coeff_le (NeZero.ne N) hM (mdiff_mul_discPow hFhol M)
      (hFper.mul (periodic_discPow_comp_ofComplex M N)) hFbd'⟩

end WLight

/-! ## 4. Rational `q`-coefficients are a faithful linear invariant -/

namespace WLight

open Complex UpperHalfPlane Function Filter
open scoped Topology Manifold ModularForm

section Flatness

open ModularForm

variable {N : ℕ}

private lemma mdiff_discB (k : ℕ) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) ((ModularForm.discriminant : ℍ → ℂ) ^ k) := by
  induction k with
  | zero =>
    rw [pow_zero]
    exact mdifferentiable_const
  | succ n ih =>
    rw [pow_succ]
    exact ih.mul CuspForm.discriminant.holo'

private lemma mdiff_finsetSum {ι : Type*} (t : Finset ι) (g : ι → ℂ) (F : ι → ℍ → ℂ)
    (h : ∀ j ∈ t, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (F j)) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (∑ j ∈ t, g j • F j) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact mdifferentiable_const
  | insert a u ha ih =>
    rw [Finset.sum_insert ha]
    exact ((h a (Finset.mem_insert_self a u)).const_smul (g a)).add
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

private lemma periodic_finsetSum {ι : Type*} (t : Finset ι) (g : ι → ℂ) (F : ι → ℍ → ℂ)
    {c : ℝ} (h : ∀ j ∈ t, Function.Periodic (F j ∘ ofComplex) c) :
    Function.Periodic ((∑ j ∈ t, g j • F j) ∘ ofComplex) c := by
  intro x
  simp only [Function.comp_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun j hj => ?_
  have h2 := h j hj x
  simp only [Function.comp_apply] at h2
  rw [h2]

private lemma bounded_finsetSum {ι : Type*} (t : Finset ι) (g : ι → ℂ) (F : ι → ℍ → ℂ)
    (h : ∀ j ∈ t, IsBoundedAtImInfty (F j)) :
    IsBoundedAtImInfty (∑ j ∈ t, g j • F j) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have h0 : (0 : ℍ → ℂ) = fun _ : ℍ => (0 : ℂ) := rfl
    rw [h0]
    exact Filter.const_boundedAtFilter _ _
  | insert a u ha ih =>
    rw [Finset.sum_insert ha]
    exact ((h a (Finset.mem_insert_self a u)).smul (g a)).add
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

private lemma analyticAt_zero_fn [NeZero N] :
    AnalyticAt ℂ (cuspFunction N (0 : ℍ → ℂ)) 0 := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  refine analyticAt_cuspFunction_zero hN' (fun x => rfl) mdifferentiable_const ?_
  have h0 : (0 : ℍ → ℂ) = fun _ : ℍ => (0 : ℂ) := rfl
  rw [h0]
  exact Filter.const_boundedAtFilter _ _

private lemma qExpansion_zero_fn [NeZero N] : qExpansion N (0 : ℍ → ℂ) = 0 := by
  have h0 : (0 : ℍ → ℂ) = (0 : ℂ) • (0 : ℍ → ℂ) := by rw [zero_smul]
  rw [h0, qExpansion_smul analyticAt_zero_fn, zero_smul]

private lemma qExpansion_finsetSum [NeZero N] {ι : Type*} (t : Finset ι) (g : ι → ℂ)
    (F : ι → ℍ → ℂ)
    (hhol : ∀ j ∈ t, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (F j))
    (hper : ∀ j ∈ t, Function.Periodic (F j ∘ ofComplex) N)
    (hbd : ∀ j ∈ t, IsBoundedAtImInfty (F j)) :
    qExpansion N (∑ j ∈ t, g j • F j) = ∑ j ∈ t, g j • qExpansion N (F j) := by
  classical
  have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  induction t using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact qExpansion_zero_fn
  | insert a u ha ih =>
    have hholu : ∀ j ∈ u, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (F j) :=
      fun j hj => hhol j (Finset.mem_insert_of_mem hj)
    have hperu : ∀ j ∈ u, Function.Periodic (F j ∘ ofComplex) N :=
      fun j hj => hper j (Finset.mem_insert_of_mem hj)
    have hbdu : ∀ j ∈ u, IsBoundedAtImInfty (F j) :=
      fun j hj => hbd j (Finset.mem_insert_of_mem hj)
    have ha1 : AnalyticAt ℂ (cuspFunction N (F a)) 0 :=
      analyticAt_cuspFunction_zero hN' (hper a (Finset.mem_insert_self a u))
        (hhol a (Finset.mem_insert_self a u)) (hbd a (Finset.mem_insert_self a u))
    have hga : AnalyticAt ℂ (cuspFunction N (g a • F a)) 0 := by
      refine analyticAt_cuspFunction_zero hN' ?_
        ((hhol a (Finset.mem_insert_self a u)).const_smul (g a)) ?_
      · intro x
        have h2 := hper a (Finset.mem_insert_self a u) x
        simp only [Function.comp_apply] at h2
        simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul]
        exact congrArg (fun z => g a * z) h2
      · exact (hbd a (Finset.mem_insert_self a u)).smul (g a)
    have hsum : AnalyticAt ℂ (cuspFunction N (∑ j ∈ u, g j • F j)) 0 :=
      analyticAt_cuspFunction_zero hN' (periodic_finsetSum u g F hperu)
        (mdiff_finsetSum u g F hholu) (bounded_finsetSum u g F hbdu)
    rw [Finset.sum_insert ha, Finset.sum_insert ha, qExpansion_add hga hsum,
      qExpansion_smul ha1, ih hholu hperu hbdu]

theorem linearIndependent_complex_of_qExpansion_rational (N : ℕ) [NeZero N]
    (K : IntermediateField ℚ ℂ) (s : Finset (ℍ → ℂ)) (m : ℕ)
    (hdata : ∀ f ∈ s, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f ∧
      Function.Periodic ((f * ModularForm.discriminant ^ m) ∘ UpperHalfPlane.ofComplex) N ∧
      IsBoundedAtImInfty (f * ModularForm.discriminant ^ m) ∧
      ∀ n : ℕ, (UpperHalfPlane.qExpansion N (f * ModularForm.discriminant ^ m)).coeff n ∈ K)
    (hind : LinearIndependent ↥K (fun w : ↥(↑s : Set (ℍ → ℂ)) => (w : ℍ → ℂ))) :
    LinearIndependent ℂ (fun w : ↥(↑s : Set (ℍ → ℂ)) => (w : ℍ → ℂ)) := by
  classical
  have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  set P : (ℍ → ℂ) → ℍ → ℂ := fun f => f * ModularForm.discriminant ^ m with hP_def
  have hPhol : ∀ f ∈ s, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (P f) := fun f hf =>
    (hdata f hf).1.mul (mdiff_discB m)
  have hPper : ∀ f ∈ s, Function.Periodic (P f ∘ ofComplex) N := fun f hf =>
    (hdata f hf).2.1
  have hPbd : ∀ f ∈ s, IsBoundedAtImInfty (P f) := fun f hf => (hdata f hf).2.2.1
  set vec : ↥(↑s : Set (ℍ → ℂ)) → ℕ → ↥K := fun w n =>
    ⟨(qExpansion N (P (w : ℍ → ℂ))).coeff n, (hdata _ w.2).2.2.2 n⟩ with hvec_def

  have hpad : ∀ (g : ↥(↑s : Set (ℍ → ℂ)) → ℂ),
      (∑ w : ↥(↑s : Set (ℍ → ℂ)), g w • P (w : ℍ → ℂ)) =
        (∑ w : ↥(↑s : Set (ℍ → ℂ)), g w • (w : ℍ → ℂ)) * ModularForm.discriminant ^ m := by
    intro g
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun w _ => ?_
    funext τ
    simp only [hP_def, Pi.smul_apply, Pi.mul_apply, Pi.pow_apply, smul_eq_mul]
    ring

  have hkill : ∀ (g : ↥(↑s : Set (ℍ → ℂ)) → ℂ),
      (∑ w, g w • (w : ℍ → ℂ)) = 0 → ∀ n : ℕ, (∑ w, g w * ((vec w n : ℂ))) = 0 := by
    intro g hg n
    have hsum0 : (∑ w : ↥(↑s : Set (ℍ → ℂ)), g w • P (w : ℍ → ℂ)) = 0 := by
      rw [hpad g, hg, zero_mul]
    have hq0 : qExpansion N (∑ w : ↥(↑s : Set (ℍ → ℂ)), g w • P (w : ℍ → ℂ)) = 0 := by
      rw [hsum0, qExpansion_zero_fn]
    rw [qExpansion_finsetSum Finset.univ g (fun w => P (w : ℍ → ℂ))
      (fun w _ => hPhol _ w.2) (fun w _ => hPper _ w.2) (fun w _ => hPbd _ w.2)] at hq0
    have h2 := congrArg (fun S => PowerSeries.coeff n S) hq0
    simpa [PowerSeries.coeff_smul, smul_eq_mul] using h2

  have hlift : ∀ (a : ↥(↑s : Set (ℍ → ℂ)) → ↥K),
      (∀ n : ℕ, (∑ w, a w * vec w n) = 0) → (∑ w, a w • (w : ℍ → ℂ)) = 0 := by
    intro a ha
    have hq0 : qExpansion N (∑ w : ↥(↑s : Set (ℍ → ℂ)), ((a w : ℂ)) • P (w : ℍ → ℂ)) = 0 := by
      rw [qExpansion_finsetSum Finset.univ (fun w => ((a w : ℂ))) (fun w => P (w : ℍ → ℂ))
        (fun w _ => hPhol _ w.2) (fun w _ => hPper _ w.2) (fun w _ => hPbd _ w.2)]
      ext n
      simp only [map_sum, PowerSeries.coeff_smul, smul_eq_mul, map_zero]
      have h1 := congrArg (fun x : ↥K => (x : ℂ)) (ha n)
      push_cast at h1
      rw [← h1]
      rfl
    have hfun0 : (∑ w : ↥(↑s : Set (ℍ → ℂ)), ((a w : ℂ)) • P (w : ℍ → ℂ)) = 0 := by
      rw [qExpansion_eq_zero_iff hN'
        (periodic_finsetSum _ _ _ (fun w _ => hPper _ w.2))
        (mdiff_finsetSum _ _ _ (fun w _ => hPhol _ w.2))
        (bounded_finsetSum _ _ _ (fun w _ => hPbd _ w.2))] at hq0
      exact hq0
    rw [hpad (fun w => ((a w : ℂ)))] at hfun0
    have hΔne : ∀ τ : ℍ, ((ModularForm.discriminant : ℍ → ℂ) ^ m) τ ≠ 0 := fun τ => by
      simp only [Pi.pow_apply]
      exact pow_ne_zero m (ModularForm.discriminant_ne_zero τ)
    have h2 : (∑ w : ↥(↑s : Set (ℍ → ℂ)), ((a w : ℂ)) • (w : ℍ → ℂ)) = 0 := by
      funext τ
      have h3 := congrFun hfun0 τ
      simp only [Pi.mul_apply, Pi.zero_apply] at h3 ⊢
      exact (mul_eq_zero.mp h3).resolve_right (hΔne τ)
    calc (∑ w : ↥(↑s : Set (ℍ → ℂ)), a w • (w : ℍ → ℂ))
        = ∑ w : ↥(↑s : Set (ℍ → ℂ)), ((a w : ℂ)) • (w : ℍ → ℂ) :=
          Finset.sum_congr rfl fun w _ => rfl
      _ = 0 := h2

  by_contra hC
  obtain ⟨g, hg0, j₀, hj₀⟩ : ∃ g : ↥(↑s : Set (ℍ → ℂ)) → ℂ,
      (∑ w, g w • (w : ℍ → ℂ)) = 0 ∧ ∃ j, g j ≠ 0 := by
    rw [Fintype.linearIndependent_iff] at hC
    push Not at hC
    obtain ⟨g, hg, j, hj⟩ := hC
    exact ⟨g, hg, j, hj⟩

  set row : ℕ → ↥(↑s : Set (ℍ → ℂ)) → ↥K := fun n w => vec w n with hrow_def
  obtain ⟨D, hD⟩ : ∃ D : Finset ℕ, ∀ n : ℕ, row n ∈
      Submodule.span ↥K (row '' ↑D : Set (↥(↑s : Set (ℍ → ℂ)) → ↥K)) := by
    have hfg : (Submodule.span ↥K (Set.range row)).FG := IsNoetherian.noetherian _
    obtain ⟨F, hF⟩ := hfg
    have hchoice : ∀ x ∈ F, ∃ Dx : Finset ℕ,
        x ∈ Submodule.span ↥K (row '' ↑Dx : Set (↥(↑s : Set (ℍ → ℂ)) → ↥K)) := by
      intro x hx
      have hxs : x ∈ Submodule.span ↥K (Set.range row) := hF ▸ Submodule.subset_span hx
      obtain ⟨T, hTsub, hxT⟩ := Submodule.mem_span_finite_of_mem_span hxs
      have hTchoice : ∀ t ∈ T, ∃ n : ℕ, row n = t := fun t ht => hTsub ht
      choose idx hidx using hTchoice
      refine ⟨T.attach.image fun t => idx t.1 t.2, Submodule.span_mono ?_ hxT⟩
      intro t ht
      have ht' : t ∈ T := ht
      refine ⟨idx t ht', ?_, hidx t ht'⟩
      simp only [Finset.coe_image, Set.mem_image]
      exact ⟨⟨t, ht'⟩, by simp, rfl⟩
    choose Dfn hDfn using hchoice
    refine ⟨F.attach.biUnion fun x => Dfn x.1 x.2, fun n => ?_⟩
    have h1 : row n ∈ Submodule.span ↥K (F : Set (↥(↑s : Set (ℍ → ℂ)) → ↥K)) := by
      rw [hF]
      exact Submodule.subset_span ⟨n, rfl⟩
    refine Submodule.span_le.mpr ?_ h1
    intro x hx
    have hx' : x ∈ F := hx
    refine Submodule.span_mono (Set.image_mono ?_) (hDfn x hx')
    intro d hd
    simp only [Finset.coe_biUnion, Set.mem_iUnion]
    exact ⟨⟨x, hx'⟩, by simp, hd⟩

  have hDdep : ¬ LinearIndependent ℂ
      (fun w : ↥(↑s : Set (ℍ → ℂ)) =>
        algebraMap ↥K ℂ ∘ (fun d : ↥(↑D : Set ℕ) => vec w (d : ℕ))) := by
    intro hLI
    refine hj₀ (Fintype.linearIndependent_iff.mp hLI g ?_ j₀)
    funext d
    simp only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul,
      Pi.zero_apply]
    exact hkill g hg0 (d : ℕ)

  have hKdep : ¬ LinearIndependent ↥K
      (fun w : ↥(↑s : Set (ℍ → ℂ)) => fun d : ↥(↑D : Set ℕ) => vec w (d : ℕ)) := by
    intro hLI
    exact hDdep (linearIndependent_algebraMap_comp_iff.mpr hLI)
  obtain ⟨a, ha0, j₁, hj₁⟩ : ∃ a : ↥(↑s : Set (ℍ → ℂ)) → ↥K,
      (∑ w, a w • fun d : ↥(↑D : Set ℕ) => vec w (d : ℕ)) = 0 ∧ ∃ j, a j ≠ 0 := by
    rw [Fintype.linearIndependent_iff] at hKdep
    push Not at hKdep
    obtain ⟨a, ha, j, hj⟩ := hKdep
    exact ⟨a, ha, j, hj⟩

  have haD : ∀ d : ℕ, d ∈ D → (∑ w, a w * vec w d) = 0 := by
    intro d hd
    have h1 := congrFun ha0 ⟨d, hd⟩
    simpa [Finset.sum_apply, smul_eq_mul] using h1
  have haAll : ∀ n : ℕ, (∑ w, a w * vec w n) = 0 := by
    intro n
    have h1 := hD n
    obtain ⟨T, hTsub, hrowT⟩ := Submodule.mem_span_finite_of_mem_span h1
    obtain ⟨cf, hcf⟩ := Submodule.mem_span_finset.mp hrowT
    have hTD : ∀ t ∈ T, ∃ d ∈ D, row d = t := by
      intro t ht
      obtain ⟨d, hd, hdt⟩ := hTsub ht
      exact ⟨d, by simpa using hd, hdt⟩
    calc (∑ w, a w * vec w n)
        = ∑ w, a w * (row n w) := by rfl
      _ = ∑ w, a w * ((∑ t ∈ T, cf t • t) w) := by rw [← hcf.2]
      _ = ∑ w, a w * (∑ t ∈ T, cf t * t w) := by
          refine Finset.sum_congr rfl fun w _ => ?_
          congr 1
          simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      _ = ∑ t ∈ T, cf t * ∑ w, a w * t w := by
          rw [Finset.sum_congr rfl fun w _ =>
            Finset.mul_sum T (fun t => cf t * t w) (a w)]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [Finset.mul_sum Finset.univ (fun w => a w * t w) (cf t)]
          refine Finset.sum_congr rfl fun w _ => ?_
          ring
      _ = 0 := by
          refine Finset.sum_eq_zero fun t ht => ?_
          obtain ⟨d, hd, hdt⟩ := hTD t ht
          rw [← hdt]
          have : (∑ w, a w * row d w) = 0 := haD d hd
          rw [this, mul_zero]
  exact hj₁ (Fintype.linearIndependent_iff.mp hind a (hlift a haAll) j₁)

end Flatness

end WLight


/-! ## 5. `WLight.levelOne_hauptmodul_package` (SET-7 order 1)

The level-one Hauptmodul/`j`/`q`-expansion-principle bundle, statement verbatim
from `Theorems/Thm_WLight_levelOne_hauptmodul_package.lean`, proof transcribed
from `P2M/Sol/S_WLight_levelOne_hauptmodul_package.lean` (1,186 lines). Helpers
are `private`; the pin's local `maxHeartbeats 3200000` is not transcribed (the
project global cap is 4,000,000). -/

namespace WLight
namespace LevelOnePkg

open Complex Real UpperHalfPlane Function Filter Polynomial Asymptotics
open ModularForm SlashInvariantForm ModularFormClass CuspForm EisensteinSeries OnePoint
open scoped MatrixGroups Manifold Topology ArithmeticFunction.sigma

section A1_levelOne_ratSpan

open scoped MatrixGroups ArithmeticFunction.sigma

private def RatQExp {k : ℤ} (f : ModularForm 𝒮ℒ k) : Prop :=
  ∀ n : ℕ, ∃ q : ℚ, (qExpansion 1 f).coeff n = (q : ℂ)

section RatCoeffClosure

private lemma ratCoeff_mul {p q : PowerSeries ℂ}
    (hp : ∀ n : ℕ, ∃ a : ℚ, p.coeff n = (a : ℂ)) (hq : ∀ n : ℕ, ∃ a : ℚ, q.coeff n = (a : ℂ)) :
    ∀ n : ℕ, ∃ a : ℚ, (p * q).coeff n = (a : ℂ) := by
  choose F hF using hp
  choose G hG using hq
  intro n
  refine ⟨∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, F ij.1 * G ij.2, ?_⟩
  rw [PowerSeries.coeff_mul]
  push_cast
  exact Finset.sum_congr rfl fun ij _ => by rw [hF, hG]

private lemma ratCoeff_sub {p q : PowerSeries ℂ}
    (hp : ∀ n : ℕ, ∃ a : ℚ, p.coeff n = (a : ℂ)) (hq : ∀ n : ℕ, ∃ a : ℚ, q.coeff n = (a : ℂ)) :
    ∀ n : ℕ, ∃ a : ℚ, (p - q).coeff n = (a : ℂ) := by
  intro n
  obtain ⟨a, ha⟩ := hp n
  obtain ⟨b, hb⟩ := hq n
  exact ⟨a - b, by rw [map_sub, ha, hb]; push_cast; ring⟩

end RatCoeffClosure

section RatGenerators

private lemma ratCoeff_E {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k) :
    ∀ n : ℕ, ∃ q : ℚ, (qExpansion 1 (E hk)).coeff n = (q : ℂ) := by
  intro n
  rw [EisensteinSeries.E_qExpansion_coeff hk hk2]
  by_cases hn : n = 0
  · exact ⟨1, by simp [hn]⟩
  · refine ⟨-(2 * k / bernoulli k) * (σ (k - 1) n : ℚ), ?_⟩
    rw [if_neg hn]
    push_cast
    ring

private def eCubeSubESq : ModularForm 𝒮ℒ 12 :=
  ModularForm.mcast (by decide) (E₄.pow 3) - ModularForm.mcast (by decide) (E₆.pow 2)

private lemma eCubeSubESq_qExpansion :
    qExpansion 1 eCubeSubESq = qExpansion 1 E₄ * qExpansion 1 E₄ * qExpansion 1 E₄ -
      qExpansion 1 E₆ * qExpansion 1 E₆ := by
  simp only [eCubeSubESq, ModularForm.coe_sub, ModularForm.coe_mcast,
    ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]
  ring

private lemma discriminant_eq_smul_eCubeSubESq :
    ModularForm.discriminant = (1 / 1728 : ℂ) • eCubeSubESq := by
  ext z
  have h := discriminant_eq_E₄_cube_sub_E₆_sq z
  simp only [Pi.smul_apply, eCubeSubESq, ModularForm.coe_sub, Pi.sub_apply,
    ModularForm.coe_mcast, ModularForm.coe_pow, Pi.pow_apply, smul_eq_mul]
  rw [h]
  ring

private lemma ratCoeff_discriminant :
    ∀ n : ℕ, ∃ q : ℚ, (qExpansion 1 ModularForm.discriminant).coeff n = (q : ℂ) := by
  have h4 : ∀ n : ℕ, ∃ q : ℚ, (qExpansion 1 E₄).coeff n = (q : ℂ) :=
    ratCoeff_E (by norm_num) (by decide)
  have h6 : ∀ n : ℕ, ∃ q : ℚ, (qExpansion 1 E₆).coeff n = (q : ℂ) :=
    ratCoeff_E (by norm_num) (by decide)
  have hmain := ratCoeff_sub (ratCoeff_mul (ratCoeff_mul h4 h4) h4) (ratCoeff_mul h6 h6)
  intro n
  obtain ⟨a, ha⟩ := hmain n
  refine ⟨(1 / 1728 : ℚ) * a, ?_⟩
  rw [discriminant_eq_smul_eCubeSubESq,
    ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL,
    PowerSeries.coeff_smul, eCubeSubESq_qExpansion, smul_eq_mul, ha]
  push_cast
  ring

private lemma ratQExp_one : RatQExp (1 : ModularForm 𝒮ℒ 0) := by
  intro n
  refine ⟨if n = 0 then 1 else 0, ?_⟩
  rw [ModularForm.qExpansion_one, PowerSeries.coeff_one]
  split <;> simp

end RatGenerators

section SpanTop

private lemma span_ratQExp_eq_top_of_forall_eq_zero {k : ℤ}
    (h : ∀ f : ModularForm 𝒮ℒ k, f = 0) :
    Submodule.span ℂ {f : ModularForm 𝒮ℒ k | RatQExp f} = ⊤ := by
  rw [eq_top_iff]
  rintro f -
  rw [h f]
  exact Submodule.zero_mem _

private theorem levelOne_ratSpan (k : ℤ) :
    Submodule.span ℂ {f : ModularForm 𝒮ℒ k | RatQExp f} = ⊤ := by
  suffices H : ∀ n : ℕ, ∀ k : ℤ, k.toNat = n →
      Submodule.span ℂ {f : ModularForm 𝒮ℒ k | RatQExp f} = ⊤ from H k.toNat k rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro k hk
  rcases lt_or_ge k 0 with hneg | hpos
  · exact span_ratQExp_eq_top_of_forall_eq_zero fun f => by
      ext z
      simpa using congrFun (ModularFormClass.levelOne_neg_weight_eq_zero hneg f) z
  rcases Int.even_or_odd k with hev | hodd
  swap
  · exact span_ratQExp_eq_top_of_forall_eq_zero fun f =>
      ModularForm.levelOne_odd_weight_eq_zero hodd f
  rcases eq_or_ne k 0 with rfl | hk0
  · rw [eq_top_iff]
    rintro f -
    obtain ⟨c, hc⟩ := ModularFormClass.levelOne_weight_zero_const f
    have hf : f = c • (1 : ModularForm 𝒮ℒ 0) := by
      ext z
      simp [congrFun hc z, ModularForm.one_coe_eq_one]
    rw [hf]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ratQExp_one)
  rcases eq_or_ne k 2 with rfl | hk2
  · refine span_ratQExp_eq_top_of_forall_eq_zero fun f => ?_
    have : Subsingleton (ModularForm 𝒮ℒ 2) :=
      rank_zero_iff.mp ModularForm.levelOne_weight_two_rank_zero
    exact Subsingleton.elim f 0

  have hk2' : k % 2 = 0 := Int.even_iff.mp hev
  have hk4 : 4 ≤ k := by omega
  have hm3 : 3 ≤ k.toNat := by omega
  have hm2 : Even k.toNat := by rw [Nat.even_iff]; omega
  set Ek : ModularForm 𝒮ℒ k := ModularForm.mcast (show ((k.toNat : ℤ)) = k by omega) (E hm3)
    with hEkdef
  have hEk_rat : RatQExp Ek := by
    intro n
    exact ratCoeff_E hm3 hm2 n
  rw [eq_top_iff]
  rintro f -
  set c₀ := (qExpansion 1 f).coeff 0 with hc₀
  have hcoe_sub : (⇑(f - c₀ • Ek) : ℍ → ℂ) = ⇑f - ⇑(c₀ • Ek) := by
    simp [ModularForm.coe_sub]
  have hcusp : (qExpansion 1 (⇑(f - c₀ • Ek) : ℍ → ℂ)).coeff 0 = 0 := by
    rw [hcoe_sub, ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL,
      ModularForm.IsGLPos.coe_smul, ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL,
      map_sub, PowerSeries.coeff_smul, hEkdef, ModularForm.qExpansion_mcast,
      EisensteinSeries.E_qExpansion_coeff_zero hm3 hm2, ← hc₀]
    simp
  set g : ModularForm 𝒮ℒ (k - 12) :=
    CuspForm.discriminantEquiv (ModularForm.toCuspForm (f - c₀ • Ek) hcusp) with hgdef
  set Ψ : ModularForm 𝒮ℒ (k - 12) →ₗ[ℂ] ModularForm 𝒮ℒ k :=
    CuspForm.toModularFormₗ.comp CuspForm.discriminantEquiv.symm.toLinearMap with hΨdef
  have hsymm : ∀ u : ModularForm 𝒮ℒ (k - 12),
      CuspForm.discriminantEquiv.symm u = CuspForm.ofMulDiscriminant u := fun u =>
    CuspForm.discriminantEquiv.symm_apply_eq.mpr (by
      ext z
      rw [CuspForm.discriminantEquiv_apply, CuspForm.ofMulDiscriminant_apply,
        mul_div_cancel_left₀ _ (ModularForm.discriminant_ne_zero z)])
  have hΨg : Ψ g = f - c₀ • Ek := by
    rw [hΨdef, hgdef, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    ext z
    simp [CuspForm.toModularFormₗ_apply, ModularForm.toCuspForm_apply]
  have hΨrat : ∀ u : ModularForm 𝒮ℒ (k - 12), RatQExp u → RatQExp (Ψ u) := by
    intro u hu
    have hcoe : ⇑(Ψ u) = ⇑CuspForm.discriminant * ⇑u := by
      funext z
      rw [hΨdef, LinearMap.comp_apply, LinearEquiv.coe_coe, hsymm u]
      simp [CuspForm.toModularFormₗ_apply, CuspForm.ofMulDiscriminant_apply,
        CuspForm.coe_discriminant]
    have hq : qExpansion 1 (Ψ u) = qExpansion 1 ModularForm.discriminant * qExpansion 1 u := by
      calc qExpansion 1 (Ψ u) = qExpansion 1 (⇑CuspForm.discriminant * ⇑u) := by rw [hcoe]
        _ = _ := ModularForm.qExpansion_mul_coe one_pos one_mem_strictPeriods_SL _ _
    intro n
    rw [hq]
    exact ratCoeff_mul ratCoeff_discriminant hu n
  have hg_mem : g ∈ Submodule.span ℂ {u : ModularForm 𝒮ℒ (k - 12) | RatQExp u} := by
    rw [IH (k - 12).toNat (by omega) (k - 12) rfl]
    exact Submodule.mem_top
  have hΨg_mem : Ψ g ∈ Submodule.span ℂ {f : ModularForm 𝒮ℒ k | RatQExp f} := by
    have h1 : Ψ g ∈ Submodule.map Ψ (Submodule.span ℂ {u : ModularForm 𝒮ℒ (k - 12) | RatQExp u}) :=
      Submodule.mem_map_of_mem hg_mem
    rw [Submodule.map_span] at h1
    refine Submodule.span_mono ?_ h1
    rintro _ ⟨u, hu, rfl⟩
    exact hΨrat u hu
  have hsplit : c₀ • Ek + Ψ g = f := by
    rw [hΨg]
    abel
  rw [← hsplit]
  exact Submodule.add_mem _
    (Submodule.smul_mem _ _ (Submodule.subset_span hEk_rat)) hΨg_mem

end SpanTop

end A1_levelOne_ratSpan

section A2_polynomial_j


open scoped MatrixGroups Manifold

private def j : ℍ → ℂ := fun z => E₄ z ^ 3 / ModularForm.discriminant z

private lemma j_mul_discriminant (z : ℍ) : j z * ModularForm.discriminant z = E₄ z ^ 3 :=
  div_mul_cancel₀ _ (ModularForm.discriminant_ne_zero z)

private theorem modularForm_eq_poly_j_mul_discriminant_pow (m : ℕ) (F : ModularForm 𝒮ℒ (12 * m)) :
    ∃ P : Polynomial ℂ, P.natDegree ≤ m ∧
      ⇑F = fun z => Polynomial.eval (j z) P * ModularForm.discriminant z ^ m := by
  induction m with
  | zero =>
    obtain ⟨c, hc⟩ := ModularFormClass.levelOne_weight_zero_const
      (ModularForm.mcast (by norm_num) F : ModularForm 𝒮ℒ 0)
    have hcoe : ⇑F = Function.const ℍ c := by rw [← hc]; rfl
    refine ⟨Polynomial.C c, by simp, funext fun z => ?_⟩
    rw [show F z = Function.const ℍ c z from congrFun hcoe z]
    simp
  | succ m IH =>
    set G : ModularForm 𝒮ℒ (12 * ((m + 1 : ℕ) : ℤ)) :=
      ModularForm.mcast (by push_cast; ring) (E₄.pow (3 * (m + 1))) with hGdef
    have hG0 : (qExpansion 1 G).coeff 0 = 1 := by
      rw [hGdef, ModularForm.qExpansion_mcast,
        ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL,
        PowerSeries.coeff_zero_eq_constantCoeff, map_pow,
        ← PowerSeries.coeff_zero_eq_constantCoeff,
        EisensteinSeries.E_qExpansion_coeff_zero (by norm_num) ⟨2, rfl⟩, one_pow]
    set c₀ := (qExpansion 1 F).coeff 0 with hc₀
    have hcoe_sub : (⇑(F - c₀ • G) : ℍ → ℂ) = ⇑F - ⇑(c₀ • G) :=
      ModularForm.coe_sub F (c₀ • G)
    have hcusp : (qExpansion 1 (⇑(F - c₀ • G) : ℍ → ℂ)).coeff 0 = 0 := by
      rw [hcoe_sub, ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL,
        ModularForm.IsGLPos.coe_smul, ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL,
        map_sub, PowerSeries.coeff_smul, hG0, ← hc₀]
      simp
    set F' : ModularForm 𝒮ℒ (12 * (m : ℤ)) :=
      ModularForm.mcast (by push_cast; ring)
        (CuspForm.discriminantEquiv (ModularForm.toCuspForm (F - c₀ • G) hcusp)) with hF'def
    obtain ⟨P', hP'deg, hP'⟩ := IH F'
    refine ⟨Polynomial.C c₀ * Polynomial.X ^ (m + 1) + P', ?_, funext fun z => ?_⟩
    · refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ (hP'deg.trans (by omega)))
      exact Polynomial.natDegree_C_mul_X_pow_le c₀ (m + 1)
    · have hdecomp : F z = c₀ * G z + (F - c₀ • G) z := by
        rw [sub_apply, smul_apply]
        simp
      have hGcoe : (⇑G : ℍ → ℂ) = (⇑E₄) ^ (3 * (m + 1)) := by
        rw [show (⇑G : ℍ → ℂ) = ⇑(E₄.pow (3 * (m + 1))) from rfl, ModularForm.coe_pow]
      have hGz : G z = E₄ z ^ (3 * (m + 1)) :=
        (congrFun hGcoe z).trans (Pi.pow_apply _ _ _)
      have hcusppart : (F - c₀ • G) z =
          ModularForm.discriminant z * (Polynomial.eval (j z) P' *
            ModularForm.discriminant z ^ m) := by
        have hF'z : (CuspForm.discriminantEquiv
            (ModularForm.toCuspForm (F - c₀ • G) hcusp)) z =
            Polynomial.eval (j z) P' * ModularForm.discriminant z ^ m := by
          rw [show (CuspForm.discriminantEquiv
              (ModularForm.toCuspForm (F - c₀ • G) hcusp)) z = F' z from rfl]
          exact congrFun hP' z
        calc (F - c₀ • G) z
            = (ModularForm.toCuspForm (F - c₀ • G) hcusp) z := rfl
          _ = ModularForm.discriminant z * (CuspForm.discriminantEquiv
              (ModularForm.toCuspForm (F - c₀ • G) hcusp)) z :=
            (ModularForm.discriminant_mul_discriminantEquiv_apply _ z).symm
          _ = _ := by rw [hF'z]
      rw [hdecomp, hGz, hcusppart, pow_mul, show E₄ z ^ 3 = j z * ModularForm.discriminant z from
        (j_mul_discriminant z).symm]
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X]
      ring


private lemma holMulDiscPow_slash (m : ℕ) (h : ℍ → ℂ)
    (hinv : ∀ γ : SL(2, ℤ), h ∣[(0 : ℤ)] γ = h) (γ : SL(2, ℤ)) :
    (h * ⇑CuspForm.discriminant ^ m) ∣[(12 * m : ℤ)] γ =
      h * ⇑CuspForm.discriminant ^ m := by
  have hD : (⇑(discPowForm m) : ℍ → ℂ) ∣[(12 * m : ℤ)] (γ : GL (Fin 2) ℝ) = ⇑(discPowForm m) :=
    (discPowForm m).slash_action_eq' _ ⟨γ, rfl⟩
  rw [discPowForm_coe] at hD
  calc (h * ⇑CuspForm.discriminant ^ m) ∣[(12 * m : ℤ)] γ
      = (h * ⇑CuspForm.discriminant ^ m) ∣[((0 : ℤ) + 12 * m)] γ := by rw [zero_add]
    _ = h ∣[(0 : ℤ)] γ * (⇑CuspForm.discriminant ^ m) ∣[(12 * m : ℤ)] γ :=
        mul_slash_SL2 0 (12 * m) γ h _
    _ = h * ⇑CuspForm.discriminant ^ m := by rw [hinv γ, SL_slash, hD]

private def holMulDiscPow (m : ℕ) (h : ℍ → ℂ) (hol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h)
    (hinv : ∀ γ : SL(2, ℤ), h ∣[(0 : ℤ)] γ = h)
    (hbd : IsBoundedAtImInfty (h * ⇑CuspForm.discriminant ^ m)) :
    ModularForm 𝒮ℒ (12 * m) where
  toFun := h * ⇑CuspForm.discriminant ^ m
  slash_action_eq' := fun _ hγ => by
    obtain ⟨γ, rfl⟩ := hγ
    have h1 := holMulDiscPow_slash m h hinv γ
    rw [SL_slash, show ((γ : GL (Fin 2) ℝ)) = mapGL ℝ γ from rfl] at h1
    exact h1
  holo' := hol.mul (by rw [← discPowForm_coe]; exact (discPowForm m).holo')
  bdd_at_cusps' := fun {c} hc => by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [isBoundedAt_iff_forall_SL2Z hc]
    intro γ _
    rw [holMulDiscPow_slash m h hinv γ]
    exact hbd

private theorem levelOne_holFn_eq_polynomial_j (m : ℕ) (h : ℍ → ℂ) (hol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h)
    (hinv : ∀ γ : SL(2, ℤ), h ∣[(0 : ℤ)] γ = h)
    (hbd : IsBoundedAtImInfty (h * ⇑CuspForm.discriminant ^ m)) :
    ∃ P : Polynomial ℂ, P.natDegree ≤ m ∧ h = fun z => Polynomial.eval (j z) P := by
  obtain ⟨P, hdeg, hP⟩ := modularForm_eq_poly_j_mul_discriminant_pow m
    (holMulDiscPow m h hol hinv hbd)
  refine ⟨P, hdeg, funext fun z => ?_⟩
  have hz := congrFun hP z
  have hΔ : ModularForm.discriminant z ^ m ≠ 0 :=
    pow_ne_zero _ (ModularForm.discriminant_ne_zero z)
  have hcancel : h z * ModularForm.discriminant z ^ m =
      Polynomial.eval (j z) P * ModularForm.discriminant z ^ m := hz
  exact mul_right_cancel₀ hΔ hcancel

end A2_polynomial_j
section A3_qexp_principle

open scoped MatrixGroups

private lemma coeff_pow_self {D : PowerSeries ℂ} (hD0 : D.coeff 0 = 0) (k : ℕ) :
    (D ^ k).coeff k = (D.coeff 1) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, PowerSeries.coeff_mul]
    rw [Finset.sum_eq_single (k, 1)]
    · rw [ih, pow_succ]
    · rintro ⟨a, b⟩ hab hne
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hab
      have hab' : a + b = k + 1 := hab
      rcases lt_or_ge a k with ha | ha
      · rw [coeff_pow_eq_zero_of_lt hD0 ha, zero_mul]
      · have hb : b = 0 ∨ b = 1 := by omega
        rcases hb with rfl | rfl
        · rw [hD0, mul_zero]
        · have hak : a = k := by omega
          exact absurd (by rw [hak]) hne
    · intro hmem
      exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.mpr
        (show (k, 1).1 + (k, 1).2 = k + 1 from rfl)) hmem

private lemma coeff_mul_pow_at_order {p D : PowerSeries ℂ} (hD0 : D.coeff 0 = 0) (k : ℕ) :
    (p * D ^ k).coeff k = p.coeff 0 * (D.coeff 1) ^ k := by
  rw [PowerSeries.coeff_mul, Finset.sum_eq_single (0, k)]
  · rw [coeff_pow_self hD0]
  · rintro ⟨a, b⟩ hab hne
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hab
    have hab' : a + b = k := hab
    rcases Nat.lt_or_ge b k with h | h
    · rw [coeff_pow_eq_zero_of_lt hD0 h, mul_zero]
    · have ha0 : a = 0 := by omega
      have hbk : b = k := by omega
      subst ha0 hbk
      exact absurd rfl hne
  · intro hmem
    exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.mpr
      (show (0, k).1 + (0, k).2 = k from Nat.zero_add k)) hmem

private lemma coeff_mul_pow_eq_zero_of_lt {p D : PowerSeries ℂ} (hD0 : D.coeff 0 = 0) {k n : ℕ}
    (hn : n < k) : (p * D ^ k).coeff n = 0 := by
  rw [PowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun ⟨a, b⟩ hab => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hab
  have hab' : a + b = n := hab
  rw [coeff_pow_eq_zero_of_lt hD0 (show b < k by omega), mul_zero]

private lemma ratCoeff_pow {p : PowerSeries ℂ} (hp : ∀ n : ℕ, ∃ a : ℚ, p.coeff n = (a : ℂ)) (k : ℕ) :
    ∀ n : ℕ, ∃ a : ℚ, (p ^ k).coeff n = (a : ℂ) := by
  induction k with
  | zero =>
    intro n
    refine ⟨if n = 0 then 1 else 0, ?_⟩
    rw [pow_zero, PowerSeries.coeff_one]
    split <;> simp
  | succ k ih =>
    rw [pow_succ]
    exact ratCoeff_mul ih hp

private def polyDiscSeries (m : ℕ) (P : Polynomial ℂ) : PowerSeries ℂ :=
  ∑ i ∈ Finset.range (m + 1),
    PowerSeries.C (P.coeff i) * (qExpansion 1 E₄) ^ (3 * i) *
      (qExpansion 1 ModularForm.discriminant) ^ (m - i)

private lemma triangular_aux (m : ℕ) :
    ∀ d : ℕ, d ≤ m → ∀ c : ℕ → ℂ,
      (∀ n : ℕ, ∃ q : ℚ, (∑ i ∈ Finset.range (d + 1),
        PowerSeries.C (c i) * (qExpansion 1 E₄) ^ (3 * i) *
          (qExpansion 1 ModularForm.discriminant) ^ (m - i)).coeff n = (q : ℂ)) →
      ∀ i : ℕ, i ≤ d → ∃ q : ℚ, c i = (q : ℂ) := by
  intro d
  induction d with
  | zero =>
    intro _ c hser i hi
    obtain rfl : i = 0 := Nat.le_zero.mp hi
    obtain ⟨q, hq⟩ := hser m
    refine ⟨q, ?_⟩
    rw [Finset.sum_range_one, Nat.mul_zero, pow_zero, mul_one, Nat.sub_zero,
      coeff_mul_pow_at_order discriminant_qExpansion_coeff_zero,
      ModularForm.discriminant_qExpansion_coeff_one, one_pow, mul_one,
      PowerSeries.coeff_zero_C] at hq
    exact hq
  | succ d ihd =>
    intro hd1 c hser
    have htop : ∃ q : ℚ, c (d + 1) = (q : ℂ) := by
      obtain ⟨q, hq⟩ := hser (m - (d + 1))
      refine ⟨q, ?_⟩
      rw [Finset.sum_range_succ, map_add] at hq
      have hlow : (∑ i ∈ Finset.range (d + 1),
          PowerSeries.C (c i) * (qExpansion 1 E₄) ^ (3 * i) *
            (qExpansion 1 ModularForm.discriminant) ^ (m - i)).coeff (m - (d + 1)) = 0 := by
        rw [map_sum]
        refine Finset.sum_eq_zero fun i hi' => ?_
        rw [Finset.mem_range] at hi'
        exact coeff_mul_pow_eq_zero_of_lt discriminant_qExpansion_coeff_zero (by omega)
      rw [hlow, zero_add, coeff_mul_pow_at_order discriminant_qExpansion_coeff_zero,
        ModularForm.discriminant_qExpansion_coeff_one, one_pow, mul_one,
        PowerSeries.coeff_C_mul, PowerSeries.coeff_zero_eq_constantCoeff, map_pow,
        ← PowerSeries.coeff_zero_eq_constantCoeff,
        EisensteinSeries.E_qExpansion_coeff_zero (by norm_num) ⟨2, rfl⟩, one_pow, mul_one] at hq
      exact hq
    intro i hi
    rcases Nat.lt_or_ge i (d + 1) with hil | hig
    · obtain ⟨qt, hqt⟩ := htop
      refine ihd (by omega) c (fun n => ?_) i (by omega)
      obtain ⟨q, hq⟩ := hser n
      have hterm : ∀ n' : ℕ, ∃ q' : ℚ, (PowerSeries.C (c (d + 1)) *
          (qExpansion 1 E₄) ^ (3 * (d + 1)) *
          (qExpansion 1 ModularForm.discriminant) ^ (m - (d + 1))).coeff n' = (q' : ℂ) := by
        refine ratCoeff_mul (ratCoeff_mul ?_
          (ratCoeff_pow (ratCoeff_E (by norm_num) (by decide)) _))
          (ratCoeff_pow ratCoeff_discriminant _)
        intro n'
        refine ⟨if n' = 0 then qt else 0, ?_⟩
        rw [PowerSeries.coeff_C]
        split <;> simp [hqt]
      obtain ⟨q', hq'⟩ := hterm n
      refine ⟨q - q', ?_⟩
      rw [Finset.sum_range_succ, map_add, hq'] at hq
      rw [eq_sub_of_add_eq hq]
      push_cast
      ring
    · obtain rfl : i = d + 1 := by omega
      exact htop

private theorem levelOne_qexp_principle (m : ℕ) (P : Polynomial ℂ) (hdeg : P.natDegree ≤ m)
    (hrat : ∀ n : ℕ, ∃ q : ℚ, (polyDiscSeries m P).coeff n = (q : ℂ)) :
    ∀ i : ℕ, ∃ q : ℚ, P.coeff i = (q : ℂ) := by
  intro i
  rcases Nat.lt_or_ge m i with him | him
  · exact ⟨0, by rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]; simp⟩
  · refine triangular_aux m m le_rfl (fun i => P.coeff i) (fun n => ?_) i him
    simpa [polyDiscSeries] using hrat n

end A3_qexp_principle
section A4_j_surjective


open scoped MatrixGroups Manifold Topology

private lemma toModularFormDisc_coe :
    (⇑(CuspForm.toModularFormₗ CuspForm.discriminant) : ℍ → ℂ) = ModularForm.discriminant := by
  funext z
  rw [CuspForm.toModularFormₗ_apply]
  exact congrFun CuspForm.coe_discriminant z

private theorem j_surjective : Function.Surjective j := by
  intro c
  by_contra hc
  push Not at hc
  set Fc : ModularForm 𝒮ℒ 12 :=
    ModularForm.mcast (by decide) (E₄.pow 3) -
      c • CuspForm.toModularFormₗ CuspForm.discriminant with hFdef
  have hFapp : ∀ z : ℍ, Fc z = E₄ z ^ 3 - c * ModularForm.discriminant z := by
    intro z
    rw [hFdef, ModularForm.sub_apply, ModularForm.IsGLPos.smul_apply, smul_eq_mul,
      CuspForm.toModularFormₗ_apply, congrFun CuspForm.coe_discriminant z,
      show (ModularForm.mcast (by decide) (E₄.pow 3) : ModularForm 𝒮ℒ 12) z = E₄ z ^ 3 from
        (congrFun (ModularForm.coe_pow E₄ 3) z).trans (Pi.pow_apply _ _ _)]
  have hnv : ∀ z : ℍ, Fc z ≠ 0 := by
    intro z h0
    rw [hFapp z, sub_eq_zero] at h0
    refine hc z ?_
    show E₄ z ^ 3 / ModularForm.discriminant z = c
    rw [h0, mul_div_cancel_right₀ _ (ModularForm.discriminant_ne_zero z)]
  have hF0 : (qExpansion 1 Fc).coeff 0 = 1 := by
    rw [hFdef, ModularForm.coe_sub,
      ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL,
      ModularForm.IsGLPos.coe_smul, ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL,
      map_sub, PowerSeries.coeff_smul, ModularForm.qExpansion_mcast,
      ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL,
      PowerSeries.coeff_zero_eq_constantCoeff, map_pow,
      ← PowerSeries.coeff_zero_eq_constantCoeff,
      EisensteinSeries.E_qExpansion_coeff_zero (by norm_num) ⟨2, rfl⟩, one_pow]
    rw [show (qExpansion 1 (⇑(CuspForm.toModularFormₗ CuspForm.discriminant) : ℍ → ℂ)).coeff 0
        = 0 from toModularFormDisc_coe ▸ discriminant_qExpansion_coeff_zero]
    simp
  set hfn : ℍ → ℂ := ⇑CuspForm.discriminant / ⇑Fc with hhdef
  have hol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) hfn := CuspForm.discriminant.holo'.div Fc.holo' hnv
  have hinv : ∀ γ : SL(2, ℤ), hfn ∣[(0 : ℤ)] γ = hfn := by
    intro γ
    have hγ : (γ : GL (Fin 2) ℝ) ∈ 𝒮ℒ := ⟨γ, rfl⟩
    rw [hhdef, show (0 : ℤ) = 12 - 12 by norm_num, div_slash_SL2, SL_slash, SL_slash,
      slash_action_eqn _ _ hγ, slash_action_eqn _ _ hγ]
  have hper := periodic_comp_ofComplex Fc one_mem_strictPeriods_SL
  have hanal := ModularFormClass.analyticAt_cuspFunction_zero Fc one_pos one_mem_strictPeriods_SL
  have htends : Tendsto ⇑Fc atImInfty (𝓝 (cuspFunction 1 ⇑Fc 0)) :=
    (hanal.continuousAt.tendsto.comp (qParam_tendsto_atImInfty one_pos)).congr
      (fun τ => SlashInvariantFormClass.eq_cuspFunction Fc τ one_mem_strictPeriods_SL one_ne_zero)
  have hcusp0 : cuspFunction 1 ⇑Fc 0 = 1 := by
    have h1 := qExpansion_coeff_zero one_pos hanal hper
    have h2 := cuspFunction_apply_zero one_pos hanal hper
    rw [h2, ← h1]
    exact hF0
  rw [hcusp0] at htends
  have hbd : IsBoundedAtImInfty hfn := by
    have hΔ0 : IsZeroAtImInfty (⇑CuspForm.discriminant : ℍ → ℂ) :=
      CuspFormClass.zero_at_infty CuspForm.discriminant
    have hFinv : Tendsto (fun z : ℍ => (Fc z)⁻¹) atImInfty (𝓝 (1 : ℂ)⁻¹) :=
      htends.inv₀ one_ne_zero
    have h1 : ((⇑CuspForm.discriminant : ℍ → ℂ)) =O[atImInfty] (fun _ => (1 : ℝ)) :=
      hΔ0.boundedAtFilter
    have h2 : (fun z : ℍ => (Fc z)⁻¹) =O[atImInfty] (fun _ => (1 : ℝ)) :=
      hFinv.isBigO_one ℝ
    have h3 : hfn = fun z => CuspForm.discriminant z * (Fc z)⁻¹ := by
      funext z
      rw [hhdef]
      exact div_eq_mul_inv _ _
    rw [IsBoundedAtImInfty, BoundedAtFilter, h3]
    have h4 := h1.mul h2
    simp only [one_mul] at h4
    exact h4
  have hbd' : IsBoundedAtImInfty (hfn * ⇑CuspForm.discriminant ^ 0) := by
    rw [show hfn * ⇑CuspForm.discriminant ^ 0 = hfn from by funext z; simp]
    exact hbd
  obtain ⟨c', hc'⟩ := ModularFormClass.levelOne_weight_zero_const
    (ModularForm.mcast (by norm_num) (holMulDiscPow 0 hfn hol hinv hbd') : ModularForm 𝒮ℒ 0)
  have hconst : ∀ z : ℍ, CuspForm.discriminant z / Fc z = c' := by
    intro z
    have := congrFun hc' z
    rw [show (ModularForm.mcast (by norm_num) (holMulDiscPow 0 hfn hol hinv hbd') :
        ModularForm 𝒮ℒ 0) z = (hfn * ⇑CuspForm.discriminant ^ 0) z from rfl] at this
    simpa [hhdef] using this
  have hΔI : CuspForm.discriminant UpperHalfPlane.I ≠ 0 := by
    rw [congrFun CuspForm.coe_discriminant UpperHalfPlane.I]
    exact ModularForm.discriminant_ne_zero _
  have hc'0 : c' ≠ 0 := by
    intro h0
    rw [h0] at hconst
    exact hΔI (by
      have := hconst UpperHalfPlane.I
      rwa [div_eq_zero_iff, or_iff_left (hnv UpperHalfPlane.I)] at this)
  have hFceq : (⇑Fc : ℍ → ℂ) = c'⁻¹ • ⇑CuspForm.discriminant := by
    funext z
    have := hconst z
    rw [div_eq_iff (hnv z)] at this
    rw [Pi.smul_apply, smul_eq_mul]
    field_simp [hc'0]
    linear_combination -this
  have hcontra : (qExpansion 1 Fc).coeff 0 = 0 := by
    rw [hFceq, qExpansion_smul (ModularFormClass.analyticAt_cuspFunction_zero
        CuspForm.discriminant one_pos one_mem_strictPeriods_SL) c'⁻¹,
      PowerSeries.coeff_smul, CuspFormClass.qExpansion_coeff_zero CuspForm.discriminant
        one_pos one_mem_strictPeriods_SL]
    simp
  rw [hF0] at hcontra
  exact one_ne_zero hcontra

end A4_j_surjective
section C6_width

open scoped UpperHalfPlane Manifold MatrixGroups
open UpperHalfPlane hiding I
open SlashInvariantFormClass ModularFormClass

namespace ModularFormClass
private theorem _root_.WLight.ModularFormClass.qExpansion_coeff_width {F : Type*} [FunLike F ℍ ℂ]
    {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} [ModularFormClass F Γ k] (f : F)
    (h1 : (1 : ℝ) ∈ Γ.strictPeriods) {N : ℕ} (hN : N ≠ 0) (n : ℕ) :
    (qExpansion N f).coeff n = if N ∣ n then (qExpansion 1 f).coeff (n / N) else 0 := by
  haveI : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods one_pos h1⟩
  exact WLight.qExpansion_coeff_width f hN (by simpa using periodic_comp_ofComplex f h1)
    (ModularFormClass.holo f) (ModularFormClass.bdd_at_infty f) n

end ModularFormClass
end C6_width
section A3K

open scoped MatrixGroups

variable (k : Subfield ℂ)

private lemma kCoeff_mul {p q : PowerSeries ℂ} (hp : ∀ n : ℕ, p.coeff n ∈ k)
    (hq : ∀ n : ℕ, q.coeff n ∈ k) : ∀ n : ℕ, (p * q).coeff n ∈ k := by
  intro n
  rw [PowerSeries.coeff_mul]
  exact sum_mem fun ij _ => mul_mem (hp ij.1) (hq ij.2)

private lemma kCoeff_pow {p : PowerSeries ℂ} (hp : ∀ n : ℕ, p.coeff n ∈ k) (m : ℕ) :
    ∀ n : ℕ, (p ^ m).coeff n ∈ k := by
  induction m with
  | zero =>
    intro n
    rw [pow_zero, PowerSeries.coeff_one]
    split <;> simp [one_mem, zero_mem]
  | succ m ih =>
    rw [pow_succ]
    exact kCoeff_mul k ih hp

private lemma kCoeff_of_rat {p : PowerSeries ℂ} (hp : ∀ n : ℕ, ∃ q : ℚ, p.coeff n = (q : ℂ)) :
    ∀ n : ℕ, p.coeff n ∈ k := by
  intro n
  obtain ⟨q, hq⟩ := hp n
  rw [hq]
  exact SubfieldClass.ratCast_mem k q

private lemma kCoeff_E4 : ∀ n : ℕ, (qExpansion 1 E₄).coeff n ∈ k :=
  kCoeff_of_rat k (ratCoeff_E (by norm_num) (by decide))

private lemma kCoeff_discriminant : ∀ n : ℕ, (qExpansion 1 ModularForm.discriminant).coeff n ∈ k :=
  kCoeff_of_rat k ratCoeff_discriminant

private lemma triangular_aux_mem (m : ℕ) :
    ∀ d : ℕ, d ≤ m → ∀ c : ℕ → ℂ,
      (∀ n : ℕ, (∑ i ∈ Finset.range (d + 1),
        PowerSeries.C (c i) * (qExpansion 1 E₄) ^ (3 * i) *
          (qExpansion 1 ModularForm.discriminant) ^ (m - i)).coeff n ∈ k) →
      ∀ i : ℕ, i ≤ d → c i ∈ k := by
  intro d
  induction d with
  | zero =>
    intro _ c hser i hi
    obtain rfl : i = 0 := Nat.le_zero.mp hi
    have hq := hser m
    rwa [Finset.sum_range_one, Nat.mul_zero, pow_zero, mul_one, Nat.sub_zero,
      coeff_mul_pow_at_order discriminant_qExpansion_coeff_zero,
      ModularForm.discriminant_qExpansion_coeff_one, one_pow, mul_one,
      PowerSeries.coeff_zero_C] at hq
  | succ d ihd =>
    intro hd1 c hser
    have htop : c (d + 1) ∈ k := by
      have hq := hser (m - (d + 1))
      rw [Finset.sum_range_succ, map_add] at hq
      have hlow : (∑ i ∈ Finset.range (d + 1),
          PowerSeries.C (c i) * (qExpansion 1 E₄) ^ (3 * i) *
            (qExpansion 1 ModularForm.discriminant) ^ (m - i)).coeff (m - (d + 1)) = 0 := by
        rw [map_sum]
        refine Finset.sum_eq_zero fun i hi' => ?_
        rw [Finset.mem_range] at hi'
        exact coeff_mul_pow_eq_zero_of_lt discriminant_qExpansion_coeff_zero (by omega)
      rwa [hlow, zero_add, coeff_mul_pow_at_order discriminant_qExpansion_coeff_zero,
        ModularForm.discriminant_qExpansion_coeff_one, one_pow, mul_one,
        PowerSeries.coeff_C_mul, PowerSeries.coeff_zero_eq_constantCoeff, map_pow,
        ← PowerSeries.coeff_zero_eq_constantCoeff,
        EisensteinSeries.E_qExpansion_coeff_zero (by norm_num) ⟨2, rfl⟩, one_pow, mul_one] at hq
    intro i hi
    rcases Nat.lt_or_ge i (d + 1) with hil | hig
    · refine ihd (by omega) c (fun n => ?_) i (by omega)
      have hq := hser n
      have hterm : (PowerSeries.C (c (d + 1)) *
          (qExpansion 1 E₄) ^ (3 * (d + 1)) *
          (qExpansion 1 ModularForm.discriminant) ^ (m - (d + 1))).coeff n ∈ k := by
        refine kCoeff_mul k (kCoeff_mul k ?_ (kCoeff_pow k (kCoeff_E4 k) _))
          (kCoeff_pow k (kCoeff_discriminant k) _) n
        intro n'
        rw [PowerSeries.coeff_C]
        split
        · exact htop
        · exact zero_mem k
      rw [Finset.sum_range_succ, map_add] at hq
      have := sub_mem hq hterm
      rwa [add_sub_cancel_right] at this
    · obtain rfl : i = d + 1 := by omega
      exact htop

private theorem levelOne_qexp_principle_mem (m : ℕ) (P : Polynomial ℂ) (hdeg : P.natDegree ≤ m)
    (hrat : ∀ n : ℕ, (polyDiscSeries m P).coeff n ∈ k) :
    ∀ i : ℕ, P.coeff i ∈ k := by
  intro i
  rcases Nat.lt_or_ge m i with him | him
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
    exact zero_mem k
  · refine triangular_aux_mem k m m le_rfl (fun i => P.coeff i) (fun n => ?_) i him
    simpa [polyDiscSeries] using hrat n

end A3K
section KBridge

open scoped MatrixGroups

private noncomputable def polyDiscForm (m : ℕ) (P : Polynomial ℂ) : ModularForm 𝒮ℒ (12 * m) :=
  ∑ i ∈ (Finset.range (m + 1)).attach,
    P.coeff i.1 • ModularForm.mcast
      (by
        have hi := Finset.mem_range.mp i.2
        rw [Nat.cast_sub (by omega : i.1 ≤ m)]
        push_cast
        ring)
      ((E₄.pow (3 * i.1)).mul (discPowForm (m - i.1)))

private lemma polyDiscForm_term_apply {m i : ℕ} (c : ℂ)
    (h : ((3 * i : ℕ) : ℤ) * 4 + 12 * ((m - i : ℕ) : ℤ) = 12 * (m : ℤ)) (τ : ℍ) :
    (c • ModularForm.mcast h ((E₄.pow (3 * i)).mul (discPowForm (m - i)))) τ =
      c * (E₄ τ ^ (3 * i) * CuspForm.discriminant τ ^ (m - i)) := by
  rw [ModularForm.IsGLPos.smul_apply, smul_eq_mul,
    congrFun (ModularForm.coe_mcast h _) τ,
    congrFun (ModularForm.coe_mul _ _) τ, Pi.mul_apply,
    congrFun (ModularForm.coe_pow E₄ (3 * i)) τ, Pi.pow_apply,
    congrFun (discPowForm_coe (m - i)) τ, Pi.pow_apply]

private lemma polyDiscForm_coe {m : ℕ} {P : Polynomial ℂ} (hdeg : P.natDegree ≤ m) :
    ⇑(polyDiscForm m P) =
      (fun τ : ℍ => Polynomial.eval (j τ) P) * ⇑CuspForm.discriminant ^ m := by
  funext τ
  have hΔ0 : CuspForm.discriminant τ ≠ 0 := by
    rw [congrFun CuspForm.coe_discriminant τ]
    exact ModularForm.discriminant_ne_zero τ
  have hsum : (polyDiscForm m P) τ = ∑ i ∈ (Finset.range (m + 1)).attach,
      P.coeff i.1 * (E₄ τ ^ (3 * i.1) * CuspForm.discriminant τ ^ (m - i.1)) := by
    rw [polyDiscForm, ← FunLike.coeAddMonoidHom_apply (F := ModularForm 𝒮ℒ (12 * m)), map_sum]
    rw [Finset.sum_apply]
    exact Finset.sum_congr rfl fun i _ => polyDiscForm_term_apply _ _ τ
  rw [hsum, Pi.mul_apply, Pi.pow_apply]
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hdeg), Finset.sum_mul,
    Finset.sum_attach (Finset.range (m + 1))
      (fun i => P.coeff i * (E₄ τ ^ (3 * i) * CuspForm.discriminant τ ^ (m - i)))]
  refine Finset.sum_congr rfl fun i hi => ?_
  have him : i ≤ m := by
    rw [Finset.mem_range] at hi
    omega
  have hj : j τ = E₄ τ ^ 3 / CuspForm.discriminant τ := by
    rw [j, congrFun CuspForm.coe_discriminant τ]
  rw [hj, div_pow, ← pow_mul, mul_comm 3 i,
    show CuspForm.discriminant τ ^ m = CuspForm.discriminant τ ^ i *
      CuspForm.discriminant τ ^ (m - i) from by rw [← pow_add, Nat.add_sub_cancel' him]]
  have hcancel : E₄ τ ^ (i * 3) / CuspForm.discriminant τ ^ i *
      (CuspForm.discriminant τ ^ i * CuspForm.discriminant τ ^ (m - i)) =
      E₄ τ ^ (i * 3) * CuspForm.discriminant τ ^ (m - i) := by
    rw [div_mul_eq_mul_div, mul_comm (CuspForm.discriminant τ ^ i) _, ← mul_assoc,
      mul_div_assoc, div_self (pow_ne_zero i hΔ0), mul_one]
  rw [mul_assoc, hcancel]

private lemma qExpansion_finset_sum {ι : Type*} (s : Finset ι) {w : ℤ}
    (f : ι → ModularForm 𝒮ℒ w) :
    qExpansion 1 ((∑ i ∈ s, f i : ModularForm 𝒮ℒ w)) = ∑ i ∈ s, qExpansion 1 (f i) := by
  induction s using Finset.cons_induction with
  | empty => simpa using qExpansion_zero 1
  | cons a s ha ih =>
    rw [Finset.sum_cons, Finset.sum_cons, ← ih]
    exact ModularForm.qExpansion_add one_pos one_mem_strictPeriods_SL (f a) (∑ i ∈ s, f i)

private theorem qExpansion_polyDiscForm (m : ℕ) (P : Polynomial ℂ) :
    qExpansion 1 (polyDiscForm m P) = polyDiscSeries m P := by
  rw [polyDiscForm, qExpansion_finset_sum, polyDiscSeries,
    ← Finset.sum_attach (Finset.range (m + 1))
      (fun i => PowerSeries.C (P.coeff i) * (qExpansion 1 E₄) ^ (3 * i) *
        (qExpansion 1 ModularForm.discriminant) ^ (m - i))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ModularForm.IsGLPos.coe_smul,
    ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL,
    ModularForm.qExpansion_mcast,
    ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]
  have hdisc : qExpansion 1 (discPowForm (m - i.1)) =
      (qExpansion 1 ModularForm.discriminant) ^ (m - i.1) := by
    rw [discPowForm, ModularForm.qExpansion_mcast,
      ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]
    have hco : (⇑(CuspForm.toModularFormₗ CuspForm.discriminant) : ℍ → ℂ) =
        ModularForm.discriminant := by
      funext z
      rw [CuspForm.toModularFormₗ_apply]
      exact congrFun CuspForm.coe_discriminant z
    rw [hco]
  rw [hdisc]
  ext n
  rw [PowerSeries.coeff_smul, smul_eq_mul, mul_assoc, PowerSeries.coeff_C_mul]

end KBridge
section KPoleSec

open scoped MatrixGroups Manifold

variable {N : ℕ}

private lemma mem_of_rat (K : IntermediateField ℚ ℂ) {x : ℂ} (h : ∃ q : ℚ, x = (q : ℂ)) : x ∈ K := by
  obtain ⟨q, rfl⟩ := h
  exact SubfieldClass.ratCast_mem K q

private def KPoleAt (K : IntermediateField ℚ ℂ) (N m : ℕ) (f : ℍ → ℂ) : Prop :=
  Function.Periodic ((f * ⇑CuspForm.discriminant ^ m) ∘ ofComplex) N ∧
    IsBoundedAtImInfty (f * ⇑CuspForm.discriminant ^ m) ∧
    ∀ n : ℕ, (qExpansion N (f * ⇑CuspForm.discriminant ^ m)).coeff n ∈ K

private def KPole (K : IntermediateField ℚ ℂ) (N : ℕ) (f : ℍ → ℂ) : Prop :=
  MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f ∧ ∃ m : ℕ, KPoleAt K N m f
private lemma qExpansion_discPow_coeff_mem (K : IntermediateField ℚ ℂ) [NeZero N] (k n : ℕ) :
    (qExpansion N (⇑CuspForm.discriminant ^ k : ℍ → ℂ)).coeff n ∈ K := by
  have h1 : qExpansion (N : ℝ) (⇑CuspForm.discriminant ^ k : ℍ → ℂ) =
      qExpansion (N : ℝ) (discPowForm k) := by
    rw [← discPowForm_coe]
  rw [h1, ModularFormClass.qExpansion_coeff_width (discPowForm k)
    one_mem_strictPeriods_SL (NeZero.ne N)]
  split
  · rw [qExpansion_one_discPowForm]
    exact mem_of_rat K (ratCoeff_pow ratCoeff_discriminant k _)
  · exact zero_mem _

private lemma KPoleAt.pad {K : IntermediateField ℚ ℂ} [NeZero N] {f : ℍ → ℂ} {m m' : ℕ}
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (hm : m ≤ m') (h : KPoleAt K N m f) : KPoleAt K N m' f := by
  obtain ⟨hper, hbd, hmem⟩ := h
  have hshape : (f * ⇑CuspForm.discriminant ^ m' : ℍ → ℂ) =
      (f * ⇑CuspForm.discriminant ^ m) * ⇑CuspForm.discriminant ^ (m' - m) := by
    funext τ
    simp only [Pi.mul_apply, Pi.pow_apply]
    rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' hm]
  refine ⟨?_, ?_, ?_⟩
  · rw [hshape]
    exact hper.mul (periodic_discPow_comp_ofComplex (m' - m) N)
  · exact IsBoundedAtImInfty.mul_discPow_mono hm hbd
  · intro n
    rw [hshape, qExpansion_mul
      (analyticAt_cuspFunction_zero_of (mdiff_mul_discPow hhol m) hper hbd)
      (analyticAt_cuspFunction_zero_of (mdiff_discPow (m' - m))
        (periodic_discPow_comp_ofComplex (m' - m) N) (isBoundedAtImInfty_discPow (m' - m))),
      PowerSeries.coeff_mul]
    exact sum_mem fun ij _ => mul_mem (hmem ij.1) (qExpansion_discPow_coeff_mem K _ ij.2)

private lemma kPole_algebraMap {K : IntermediateField ℚ ℂ} [NeZero N] (c : ↥K) :
    KPole K N (algebraMap ↥K (ℍ → ℂ) c) := by
  have hshape : ((algebraMap ↥K (ℍ → ℂ) c) * ⇑CuspForm.discriminant ^ 0 : ℍ → ℂ) =
      (c : ℂ) • (1 : ℍ → ℂ) := by
    funext τ
    simp only [Pi.mul_apply, pow_zero, mul_one, Pi.smul_apply, Pi.one_apply,
      smul_eq_mul]
    rfl
  have hone_bd : IsBoundedAtImInfty (1 : ℍ → ℂ) := by
    have h1 : (1 : ℍ → ℂ) = fun _ : ℍ => (1 : ℂ) := rfl
    rw [h1]
    exact const_boundedAtFilter _ _
  refine ⟨mdifferentiable_const, 0, ?_, ?_, ?_⟩
  · rw [hshape]
    intro x
    rfl
  · rw [hshape]
    have hc : ((c : ℂ) • (1 : ℍ → ℂ)) = fun _ : ℍ => (c : ℂ) := by
      funext τ
      simp
    rw [hc]
    exact const_boundedAtFilter _ _
  · intro n
    have han : AnalyticAt ℂ (cuspFunction N (1 : ℍ → ℂ)) 0 :=
      analyticAt_cuspFunction_zero_of (g := (1 : ℍ → ℂ)) mdifferentiable_const
        (periodic_one_fn N) hone_bd
    rw [hshape, qExpansion_smul han,
      qExpansion_one, PowerSeries.coeff_smul, smul_eq_mul, PowerSeries.coeff_one]
    split
    · rw [mul_one]
      exact c.2
    · rw [mul_zero]
      exact zero_mem _

private lemma KPole.add {K : IntermediateField ℚ ℂ} [NeZero N] {f g : ℍ → ℂ} (hf : KPole K N f)
    (hg : KPole K N g) : KPole K N (f + g) := by
  obtain ⟨hf1, m1, hfd⟩ := hf
  obtain ⟨hg1, m2, hgd⟩ := hg
  obtain ⟨hfper, hfbd, hfmem⟩ := hfd.pad hf1 (le_max_left m1 m2)
  obtain ⟨hgper, hgbd, hgmem⟩ := hgd.pad hg1 (le_max_right m1 m2)
  have hshape : ((f + g) * ⇑CuspForm.discriminant ^ max m1 m2 : ℍ → ℂ) =
      f * ⇑CuspForm.discriminant ^ max m1 m2 + g * ⇑CuspForm.discriminant ^ max m1 m2 := by
    funext τ
    simp [add_mul]
  refine ⟨hf1.add hg1, max m1 m2, ?_, ?_, ?_⟩
  · rw [hshape]
    exact hfper.add hgper
  · rw [hshape]
    exact hfbd.add hgbd
  · intro n
    rw [hshape, qExpansion_add
      (analyticAt_cuspFunction_zero_of (mdiff_mul_discPow hf1 _) hfper hfbd)
      (analyticAt_cuspFunction_zero_of (mdiff_mul_discPow hg1 _) hgper hgbd),
      map_add]
    exact add_mem (hfmem n) (hgmem n)

private lemma KPole.mul {K : IntermediateField ℚ ℂ} [NeZero N] {f g : ℍ → ℂ} (hf : KPole K N f)
    (hg : KPole K N g) : KPole K N (f * g) := by
  obtain ⟨hf1, m1, hfper, hfbd, hfmem⟩ := hf
  obtain ⟨hg1, m2, hgper, hgbd, hgmem⟩ := hg
  have hshape : ((f * g) * ⇑CuspForm.discriminant ^ (m1 + m2) : ℍ → ℂ) =
      (f * ⇑CuspForm.discriminant ^ m1) * (g * ⇑CuspForm.discriminant ^ m2) := by
    funext τ
    simp only [Pi.mul_apply, Pi.pow_apply, pow_add]
    ring
  refine ⟨hf1.mul hg1, m1 + m2, ?_, ?_, ?_⟩
  · rw [hshape]
    exact hfper.mul hgper
  · rw [hshape]
    exact hfbd.mul hgbd
  · intro n
    rw [hshape, qExpansion_mul
      (analyticAt_cuspFunction_zero_of (mdiff_mul_discPow hf1 _) hfper hfbd)
      (analyticAt_cuspFunction_zero_of (mdiff_mul_discPow hg1 _) hgper hgbd),
      PowerSeries.coeff_mul]
    exact sum_mem fun ij _ => mul_mem (hfmem ij.1) (hgmem ij.2)

private theorem kPole_invariant_eq_polynomial_j_mem {K : IntermediateField ℚ ℂ} [NeZero N]
    {a : ℍ → ℂ} (hk : KPole K N a) (hinv : ∀ γ : SL(2, ℤ), a ∣[(0 : ℤ)] γ = a) :
    ∃ P : Polynomial ℂ, (∀ i, P.coeff i ∈ K) ∧ a = fun τ => Polynomial.eval (j τ) P := by
  obtain ⟨hhol, m, hper, hbd, hmem⟩ := hk
  obtain ⟨P, hdeg, hP⟩ := levelOne_holFn_eq_polynomial_j m a hhol hinv hbd
  have hfn : (a * ⇑CuspForm.discriminant ^ m : ℍ → ℂ) = ⇑(polyDiscForm m P) := by
    rw [hP]
    exact (polyDiscForm_coe hdeg).symm
  have h1 : ∀ n, (qExpansion 1 (polyDiscForm m P)).coeff n ∈ K := by
    intro n
    have hw := qExpansion_coeff_width (⇑(polyDiscForm m P) : ℍ → ℂ) (NeZero.ne N)
      (SlashInvariantFormClass.periodic_comp_ofComplex _ one_mem_strictPeriods_SL)
      (polyDiscForm m P).holo' (ModularFormClass.bdd_at_infty _) (N * n)
    rw [if_pos ⟨n, rfl⟩, Nat.mul_div_cancel_left n (Nat.pos_of_ne_zero (NeZero.ne N))] at hw
    rw [← hw]
    have hm := hmem (N * n)
    rwa [hfn] at hm
  refine ⟨P, fun i => ?_, hP⟩
  have hmem1 := levelOne_qexp_principle_mem K.toSubfield m P hdeg (fun n => by
    rw [← qExpansion_polyDiscForm]
    exact h1 n) i
  exact hmem1
end KPoleSec

theorem _root_.WLight.levelOne_hauptmodul_package :

    (∀ (m : ℕ) (h : ℍ → ℂ), MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h →
      (∀ γ : SL(2, ℤ), h ∣[(0 : ℤ)] γ = h) →
      IsBoundedAtImInfty (h * ModularForm.discriminant ^ m) →
      ∃ P : Polynomial ℂ, P.natDegree ≤ m ∧
        h = fun τ => Polynomial.eval (ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ) P) ∧

    (∀ (k : IntermediateField ℚ ℂ) (N : ℕ), N ≠ 0 → ∀ (m : ℕ) (h : ℍ → ℂ),
      MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h →
      (∀ γ : SL(2, ℤ), h ∣[(0 : ℤ)] γ = h) →
      Function.Periodic ((h * ModularForm.discriminant ^ m) ∘ ofComplex) N →
      IsBoundedAtImInfty (h * ModularForm.discriminant ^ m) →
      (∀ n : ℕ, (qExpansion N (h * ModularForm.discriminant ^ m)).coeff n ∈ k) →
      ∃ P : Polynomial ℂ, P.natDegree ≤ m ∧ (∀ i, P.coeff i ∈ k) ∧
        h = fun τ => Polynomial.eval (ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ) P) ∧

    Function.Surjective (fun τ : ℍ => ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ) ∧

    (∀ (m : ℕ) (P : Polynomial ℂ), P.natDegree ≤ m →
      (∀ n : ℕ, ∃ q : ℚ, (∑ i ∈ Finset.range (m + 1),
          PowerSeries.C (P.coeff i) * qExpansion 1 ⇑ModularForm.E₄ ^ (3 * i) *
            qExpansion 1 ModularForm.discriminant ^ (m - i)).coeff n = (q : ℂ)) →
      ∀ i : ℕ, ∃ q : ℚ, P.coeff i = (q : ℂ)) ∧

    (∀ (k : IntermediateField ℚ ℂ) (m : ℕ) (P : Polynomial ℂ), P.natDegree ≤ m →
      (∀ n : ℕ, (∑ i ∈ Finset.range (m + 1),
          PowerSeries.C (P.coeff i) * qExpansion 1 ⇑ModularForm.E₄ ^ (3 * i) *
            qExpansion 1 ModularForm.discriminant ^ (m - i)).coeff n ∈ k) →
      ∀ i : ℕ, P.coeff i ∈ k) := by
    have hdisc : (ModularForm.discriminant : ℍ → ℂ) = ⇑CuspForm.discriminant :=
      CuspForm.coe_discriminant.symm
    refine ⟨?_, ?_, j_surjective, ?_, ?_⟩
    · intro m h hol hinv hbd
      rw [hdisc] at hbd
      exact levelOne_holFn_eq_polynomial_j m h hol hinv hbd
    · intro k N hN m h hol hinv hper hbd hmem
      haveI : NeZero N := ⟨hN⟩
      rw [hdisc] at hper hbd hmem
      obtain ⟨P, hdeg, hP⟩ := levelOne_holFn_eq_polynomial_j m h hol hinv hbd
      obtain ⟨P', hP'k, hP'⟩ := kPole_invariant_eq_polynomial_j_mem
        (K := k) ⟨hol, m, hper, hbd, hmem⟩ hinv
      have hPP' : P = P' := by
        apply Polynomial.funext
        intro c
        obtain ⟨τ, rfl⟩ := j_surjective c
        have h1 := congrFun hP τ
        have h2 := congrFun hP' τ
        rw [← h1, h2]
      exact ⟨P, hdeg, hPP' ▸ hP'k, hP⟩
    · intro m P hdeg hrat
      exact levelOne_qexp_principle m P hdeg (by simpa [polyDiscSeries] using hrat)
    · intro k m P hdeg hmem
      exact levelOne_qexp_principle_mem k.toSubfield m P hdeg
        (by simpa [polyDiscSeries] using hmem)

  end R3Bridge

  end

end LevelOnePkg
end WLight
