/-
Integrality over `ℂ[j̄]` bounds the analytic order of a modular form at every point.

If two modular forms `g`, `h` are related by a Laurent series `X` through their
`q`-expansions, `X · ψ h = ψ g`, and `X ^ 6 · j̄ ^ (4m) · (j̄ - 1728) ^ (3m)` is integral
over `ℂ[j̄] ⊆ ℂ((q))`, then for every `τ ∈ ℍ` the form `g · (E₄²E₆) ^ m` vanishes at `τ`
at most as deep as `h · Δ ^ m` does. This is the local form of the standard passage
from an integral dependence relation over `ℂ[j]` to an inequality of divisors, and it
is what builds modular and cusp forms with a prescribed `q`-expansion: the two nodes it
feeds are `exists_modularForm_gamma1_qExpansion_eq_mul_thetaL_pow_of_isIntegral` and
`exists_cuspForm_qExpansion_eq_mul_thetaL_pow_of_isIntegral_qExpFunctionFieldC`.

`ANb.core` is the engine, at the level of the `ANb` dictionary (a normalised form
`𝔤 : 𝒩`, its `q`-expansion `ψ`, its complex realisation `toC`): the integral relation
`∑ i, pᵢ · Y ^ i = 0` for `Y = X ^ 6 · j̄ ^ (4w) · (j̄ - 1728) ^ (3w)`, with `pᵢ` the
image of a polynomial in `j̄`, is turned into the single identity

`P ^ (6n) · Δ ^ m + ∑ i, Cᵢ · (P ^ (6i) · (Q ^ 6 · Δ ^ w) ^ (n-i)) = 0`

between the complex functions realising `𝔤` and `𝔥` — the `Cᵢ` absorb the coefficients
`pᵢ` through `j̄ · Δ = E₄³`, which is what makes them come out divisible by `Δ ^ m` — and
`order_le_of_identity` reads the order inequality off it.

After FLT's `P2M/Sol/S_ModularCurve_analyticOrderAt_le_of_isIntegral_adjoin_jqModC_pow.lean`
(409 ln, of which 39 declarations are the shared `ANb` dictionary of
`ModularCurve/Analytic/ANb.lean`), pinned at `aa2d8b3`:
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_analyticOrderAt_le_of_isIntegral_adjoin_jqModC_pow.lean>.

Assumes `ModularCurve/Analytic/ANb.lean` (the dictionary: `𝒩`, `ψ`, `toC`, `𝔞`/`𝔟`/`𝔡`,
`J_mul_D`, `J_sub_mul_D`, `order_le_of_identity`) and `ModularForms/SturmBound.lean`'s
`strictPeriods` API.

spec-pin: Theorems/Thm_ModularCurve_analyticOrderAt_le_of_isIntegral_adjoin_jqModC_pow.lean
spec-pin: P2M/Sol/S_ModularCurve_analyticOrderAt_le_of_isIntegral_adjoin_jqModC_pow.lean   -- comparable copy
-/
import FLTForHuman.ModularCurve.Analytic.ANb
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula

set_option autoImplicit false

-- The pin's wrapper carries `hm : 1 ≤ m`, which its proof does not use.
set_option linter.unusedVariables false

noncomputable section

open UpperHalfPlane ModularCurve AlgebraicCurve
open scoped MatrixGroups ModularForm Manifold

namespace ANb

local notation "𝒩" => niceSubalgebra
local notation "𝐉" => ModularCurve.coeffEmb ℂ ModularCurve.jq

/-- **Integrality bounds the analytic order.** See the module header: the relation
`X · ψ 𝔥 = ψ 𝔤` plus the integral dependence of `X ^ 6 · 𝐉 ^ (4w) · (𝐉 - 1728) ^ (3w)`
gives an identity between the complex functions `toC (𝔤 * (𝔞 ^ 2 * 𝔟) ^ w)` and
`toC (𝔥 * 𝔡 ^ w) · Δ ^ w`-powers to which `order_le_of_identity` applies. -/

theorem core (w : ℕ) (𝔤 𝔥 : 𝒩) (X : LaurentSeries ℂ) (hX : X * ψ 𝔥 = ψ 𝔤)
    (h₁ : IsIntegral (Algebra.adjoin ℂ ({𝐉} : Set (LaurentSeries ℂ)))
      (X ^ 6 * 𝐉 ^ (4 * w) * (𝐉 - algebraMap ℂ (LaurentSeries ℂ) 1728) ^ (3 * w)))
    (τ : ℍ) :
    analyticOrderAt (toC (𝔥 * 𝔡 ^ w)) (τ : ℂ) ≤ analyticOrderAt (toC (𝔤 * (𝔞 ^ 2 * 𝔟) ^ w)) (τ : ℂ) := by
  classical

  have e1 : ∀ (Xx Jj T H D : LaurentSeries ℂ),
      (Xx ^ 6 * Jj ^ (4 * w) * T ^ (3 * w)) * ((H * D ^ w) ^ 6 * D ^ w)
        = (Xx * H) ^ 6 * ((Jj * D) ^ 4 * (T * D) ^ 3) ^ w := by
    intro Xx Jj T H D
    ring
  have e2 : ∀ (G A B : LaurentSeries ℂ),
      G ^ 6 * ((A ^ 3) ^ 4 * (B ^ 2) ^ 3) ^ w = (G * (A ^ 2 * B) ^ w) ^ 6 := by
    intro G A B
    ring
  have key1 : (X ^ 6 * 𝐉 ^ (4 * w) * (𝐉 - algebraMap ℂ (LaurentSeries ℂ) 1728) ^ (3 * w)) *
      ((ψ 𝔥 * ψ 𝔡 ^ w) ^ 6 * ψ 𝔡 ^ w) = (ψ 𝔤 * (ψ 𝔞 ^ 2 * ψ 𝔟) ^ w) ^ 6 := by
    rw [e1, hX, J_mul_D, J_sub_mul_D, e2]

  obtain ⟨p, hpm, hpev⟩ := h₁
  rw [hpm.as_sum] at hpev
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_finsetSum,
    Polynomial.eval₂_mul, Polynomial.eval₂_C] at hpev
  set R := Algebra.adjoin ℂ ({𝐉} : Set (LaurentSeries ℂ)) with hR
  set Y := X ^ 6 * 𝐉 ^ (4 * w) * (𝐉 - algebraMap ℂ (LaurentSeries ℂ) 1728) ^ (3 * w) with hY
  set n := p.natDegree with hn
  clear_value Y

  have hmem : ∀ i, ∃ c : Polynomial ℂ,
      Polynomial.aeval (𝐉) c = algebraMap R (LaurentSeries ℂ) (p.coeff i) := by
    intro i
    have hi' : algebraMap R (LaurentSeries ℂ) (p.coeff i) ∈ (Polynomial.aeval (R := ℂ) (𝐉)).range := by
      rw [← Algebra.adjoin_singleton_eq_range_aeval]
      exact (p.coeff i).2
    exact hi'
  choose c hc using hmem
  set m := ∑ i ∈ Finset.range n, (c i).natDegree with hm
  have hdeg : ∀ i ∈ Finset.range n, (c i).natDegree ≤ m := fun i hi =>
    Finset.single_le_sum (f := fun j => (c j).natDegree) (fun j _ => Nat.zero_le _) hi

  let Cn : ℕ → 𝒩 := fun i =>
    ∑ l ∈ Finset.range ((c i).natDegree + 1), algebraMap ℂ 𝒩 ((c i).coeff l) * (𝔡 ^ (m - l) * 𝔞 ^ (3 * l))
  have key3 : ∀ i ∈ Finset.range n, ψ 𝔡 ^ m * algebraMap R (LaurentSeries ℂ) (p.coeff i) = ψ (Cn i) := by
    intro i hi
    simp only [Cn, map_sum, map_mul, map_pow, AlgHom.commutes]
    rw [← hc i, Polynomial.aeval_eq_sum_range, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l hl => ?_
    have hlm : l ≤ m := (Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)).trans (hdeg i hi)
    rw [Algebra.smul_def, mul_left_comm]
    congr 1
    calc ψ 𝔡 ^ m * 𝐉 ^ l = ψ 𝔡 ^ (m - l) * ψ 𝔡 ^ l * 𝐉 ^ l := by
          rw [← pow_add, Nat.sub_add_cancel hlm]
      _ = ψ 𝔡 ^ (m - l) * (𝐉 * ψ 𝔡) ^ l := by rw [mul_pow]; ring
      _ = ψ 𝔡 ^ (m - l) * ψ 𝔞 ^ (3 * l) := by rw [J_mul_D, ← pow_mul]

  let P : 𝒩 := 𝔤 * (𝔞 ^ 2 * 𝔟) ^ w
  let Q : 𝒩 := 𝔥 * 𝔡 ^ w
  have k1 : Y * (ψ Q ^ 6 * ψ 𝔡 ^ w) = ψ P ^ 6 := by
    simp only [P, Q, map_mul, map_pow]
    exact key1
  have key2 : ∀ i ≤ n, (ψ Q ^ 6 * ψ 𝔡 ^ w) ^ n * Y ^ i = ψ P ^ (6 * i) * (ψ Q ^ 6 * ψ 𝔡 ^ w) ^ (n - i) := by
    intro i hi
    have e : (ψ Q ^ 6 * ψ 𝔡 ^ w) ^ n = (ψ Q ^ 6 * ψ 𝔡 ^ w) ^ i * (ψ Q ^ 6 * ψ 𝔡 ^ w) ^ (n - i) := by
      rw [← pow_add, Nat.add_sub_cancel' hi]
    calc (ψ Q ^ 6 * ψ 𝔡 ^ w) ^ n * Y ^ i = (Y * (ψ Q ^ 6 * ψ 𝔡 ^ w)) ^ i * (ψ Q ^ 6 * ψ 𝔡 ^ w) ^ (n - i) := by
          rw [e, mul_pow Y (ψ Q ^ 6 * ψ 𝔡 ^ w) i]; ring
      _ = ψ P ^ (6 * i) * (ψ Q ^ 6 * ψ 𝔡 ^ w) ^ (n - i) := by rw [k1, ← pow_mul]

  let E : 𝒩 := P ^ (6 * n) * 𝔡 ^ m + ∑ i ∈ Finset.range n, Cn i * (P ^ (6 * i) * (Q ^ 6 * 𝔡 ^ w) ^ (n - i))
  have hE : ψ E = (ψ Q ^ 6 * ψ 𝔡 ^ w) ^ n * ψ 𝔡 ^ m *
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

  have hC := congrArg toC hE0
  simp only [E, map_add, map_sum, map_mul, map_pow, map_zero] at hC
  exact order_le_of_identity (analyticAt_toC P τ) (analyticAt_toC Q τ) ((analyticAt_toC 𝔡 τ).pow m)
    ((analyticAt_toC 𝔡 τ).pow w) (fun i _ => analyticAt_toC (Cn i) τ)
    (by rw [Pi.pow_apply, toC𝔡_apply]; exact pow_ne_zero _ (ModularForm.discriminant_ne_zero τ))
    (by rw [Pi.pow_apply, toC𝔡_apply]; exact pow_ne_zero _ (ModularForm.discriminant_ne_zero τ)) hC

end ANb

namespace ModularCurve

open ANb in
/-- **Integrality over `ℂ[j̄]` bounds the analytic order** — the pin's headline, from its
`Theorems/` wrapper. `ANb.core` does the work; the reduction from `jqModC ℂ` to
`coeffEmb ℂ jq` is the dictionary's `coeffEmb_jq`. -/
theorem analyticOrderAt_le_of_isIntegral_adjoin_jqModC_pow
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ) {k : ℤ} (m : ℕ) (hm : 1 ≤ m)
    (g h : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (X : LaurentSeries ℂ)
    (hX : X * ((UpperHalfPlane.qExpansion 1 (h : UpperHalfPlane → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) = ((UpperHalfPlane.qExpansion 1 (g : UpperHalfPlane → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ))
    (h₁ : IsIntegral (Algebra.adjoin ℂ ({ModularCurve.jqModC ℂ} : Set (LaurentSeries ℂ)))
      (X ^ 6 * ModularCurve.jqModC ℂ ^ (4 * m) * (ModularCurve.jqModC ℂ - algebraMap ℂ (LaurentSeries ℂ) 1728) ^ (3 * m)))
    (τ : UpperHalfPlane) :
    analyticOrderAt ((fun z : UpperHalfPlane => h z * ModularForm.discriminant z ^ m) ∘ UpperHalfPlane.ofComplex) (τ : ℂ) ≤
      analyticOrderAt ((fun z : UpperHalfPlane => g z * (ModularForm.E₄ z ^ 2 * ModularForm.E₆ z) ^ m) ∘ UpperHalfPlane.ofComplex) (τ : ℂ) := by
  have h₁' : IsIntegral (Algebra.adjoin ℂ ({ModularCurve.coeffEmb ℂ ModularCurve.jq} : Set (LaurentSeries ℂ)))
      (X ^ 6 * ModularCurve.coeffEmb ℂ ModularCurve.jq ^ (4 * m) *
        (ModularCurve.coeffEmb ℂ ModularCurve.jq - algebraMap ℂ (LaurentSeries ℂ) 1728) ^ (3 * m)) := by
    rw [ANb.coeffEmb_jq]; exact h₁
  exact ANb.core m (ANb.ofMF g (ANb.one_mem_strictPeriods_of_T_mem hT)) (ANb.ofMF h (ANb.one_mem_strictPeriods_of_T_mem hT))
    X hX h₁' τ

end ModularCurve

#print axioms ModularCurve.analyticOrderAt_le_of_isIntegral_adjoin_jqModC_pow
