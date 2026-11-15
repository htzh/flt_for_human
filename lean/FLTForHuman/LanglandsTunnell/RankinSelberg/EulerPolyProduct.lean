/-
  The Rankin–Selberg Euler polynomial's inverse product: for a number field `K`, a finite set `S` of
  places, Hecke data `a b a' b'` and a real `κ` with `‖a v‖, ‖b v‖, ‖a' v‖, ‖b' v‖ ≤ |v| ^ κ`, the
  product `∏'_{v ∉ S} (P_v(|v| ^ (-s)))⁻¹` is multiplicable, differentiable and non-zero on a
  half-plane `re s > σ₀`.

  `P_v` is the pin's degree-six Euler polynomial `rsEulerPoly (a v) (b v) (a' v) (b' v) 0` — the
  definition layer's `FLTForHuman.LanglandsTunnell.RankinSelberg.Euler`, imported here, not restated —
  read at `|v| ^ (-s)`; at the fifth argument `0` the degree-six term drops out, and after splitting
  `a v = α + β`, `b v = α β`, `a' v = γ + δ`, `b' v = γ δ` the polynomial is the product of the four
  linear factors `(1 - α γ X) (1 - α δ X) (1 - β γ X) (1 - β δ X)`. The estimate that makes the
  product converge is that every root of the quadratic `X² - a X + b` has norm `≤ max 1 (‖a‖ + ‖b‖)`,
  so each Satake parameter is dominated by `|v| ^ κ`, and the shift `t = 2 κ' + 2` makes each
  Rankin–Selberg factor of the form `1 - z v * |v| ^ (-(s - t))` with `‖z v‖ ≤ 1` — the degree-one
  case the port already proves (`NumberField.ZetaEuler`). The row is the pin's `solution`, read at
  the row's name; it is the pin's own specialization of the general statement `main` of the same
  file, and both are declared here.

  spec-pin: P2M/Sol/S_LanglandsTunnell_RankinSelberg_exists_multipliable_differentiableOn_tprod_inv_eval_rsEulerPoly_of_norm_le_rpow.lean
  spec-pin: Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_multipliable_differentiableOn_tprod_inv_eval_rsEulerPoly_of_norm_le_rpow.lean
-/
import FLTForHuman.LanglandsTunnell.RankinSelberg.Euler
import FLTForHuman.NumberTheory.LSeries.DedekindZetaEulerProduct
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.Topology.Algebra.InfiniteSum.Basic

set_option autoImplicit false

noncomputable section

open IsDedekindDomain NumberField Polynomial
open scoped BigOperators

namespace LanglandsTunnell.RankinSelberg

/-- Every complex number is the sum and product of the two roots of `X² - a X + b`: the quadratic
always splits over `ℂ`. -/
theorem exists_roots (a b : ℂ) : ∃ α β : ℂ, α + β = a ∧ α * β = b := by
  obtain ⟨d, hd⟩ := IsAlgClosed.exists_eq_mul_self (a ^ 2 - 4 * b)
  exact ⟨(a + d) / 2, (a - d) / 2, by ring, by linear_combination (1 / 4 : ℂ) * hd⟩

/-- A root of `X² - a X + b` is bounded by `max 1 (‖a‖ + ‖b‖)`: outside the unit disc the equation
`α² = a α - b` gives `‖α‖ ≤ ‖a‖ + ‖b‖`, and inside it the bound is `1`. -/
theorem norm_root_le {a b α β : ℂ} (h1 : α + β = a) (h2 : α * β = b) :
    ‖α‖ ≤ max 1 (‖a‖ + ‖b‖) := by
  by_cases hα : ‖α‖ ≤ 1
  · exact hα.trans (le_max_left _ _)
  · push Not at hα
    refine le_trans ?_ (le_max_right _ _)
    have key : α ^ 2 = a * α - b := by rw [← h1, ← h2]; ring
    have hn : ‖α‖ ^ 2 ≤ ‖a‖ * ‖α‖ + ‖b‖ := by
      calc ‖α‖ ^ 2 = ‖α ^ 2‖ := (norm_pow _ _).symm
        _ = ‖a * α - b‖ := by rw [key]
        _ ≤ ‖a * α‖ + ‖b‖ := norm_sub_le _ _
        _ = ‖a‖ * ‖α‖ + ‖b‖ := by rw [norm_mul]
    have hb : ‖b‖ ≤ ‖b‖ * ‖α‖ := le_mul_of_one_le_right (norm_nonneg _) hα.le
    nlinarith [norm_nonneg a, norm_nonneg b, norm_nonneg α]

/-- On Satake data split as `a = α + β`, `b = α β` and `eᵢ = γⁱ`-symmetric data split as
`a' = γ + δ`, `b' = γ δ`, the Euler polynomial at its fifth argument `0` factors into the four
linear factors of the Rankin–Selberg local integral. -/
theorem eval_rsEulerPoly_eq (α β γ δ x : ℂ) :
    (LanglandsTunnell.RankinSelberg.rsEulerPoly (α + β) (α * β) (γ + δ) (γ * δ) 0).eval x =
      (1 - α * γ * x) * (1 - α * δ * x) * (1 - β * γ * x) * (1 - β * δ * x) := by
  simp only [LanglandsTunnell.RankinSelberg.rsEulerPoly, eval_add, eval_mul, eval_C, eval_X, eval_pow]
  ring

/-- Convergence, holomorphy and non-vanishing of the partial Rankin–Selberg Euler product: under the
polynomial bound `‖a v‖, ‖b v‖, ‖a' v‖, ‖b' v‖ ≤ |v| ^ κ`, every factor's inverse is `1 - z v * |v| ^
(-(s - t))` with `‖z v‖ ≤ 1` after the shift `t = 2 κ' + 2`, so the degree-one Euler product theorem
applies four times over. -/
theorem main (K : Type) [Field K] [NumberField K] (S : Finset (HeightOneSpectrum (𝓞 K)))
    (a b a' b' : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} → ℂ) (κ : ℝ)
    (hbd : ∀ v, ‖a v‖ ≤ ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ κ ∧ ‖b v‖ ≤ ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ κ ∧
      ‖a' v‖ ≤ ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ κ ∧ ‖b' v‖ ≤ ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ κ) :
    ∃ σ₀ : ℝ,
      (∀ s : ℂ, σ₀ < s.re →
        Multipliable (fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} =>
          ((LanglandsTunnell.RankinSelberg.rsEulerPoly (a v) (b v) (a' v) (b' v) 0).eval
            (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹)) ∧
      DifferentiableOn ℂ (fun s : ℂ => ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S},
          ((LanglandsTunnell.RankinSelberg.rsEulerPoly (a v) (b v) (a' v) (b' v) 0).eval
            (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) {s : ℂ | σ₀ < s.re} ∧
      (∀ s : ℂ, σ₀ < s.re →
        (∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S},
          ((LanglandsTunnell.RankinSelberg.rsEulerPoly (a v) (b v) (a' v) (b' v) 0).eval
            (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) ≠ 0) := by
  classical

  choose α β hαβ using fun v => exists_roots (a v) (b v)
  choose γ δ hγδ using fun v => exists_roots (a' v) (b' v)
  set κ' : ℝ := max κ 0 with hκ'
  set t : ℝ := 2 * κ' + 2 with ht

  have hN2 : ∀ v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}, (2 : ℝ) ≤ ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) := by
    intro v
    have h0 : Ideal.absNorm v.1.asIdeal ≠ 0 := by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.1.ne_bot
    have h1 : Ideal.absNorm v.1.asIdeal ≠ 1 := by rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.1.isPrime.ne_top
    have : 2 ≤ Ideal.absNorm v.1.asIdeal := by omega
    exact_mod_cast this
  have hNpos : ∀ v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}, (0 : ℝ) < ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) :=
    fun v => lt_of_lt_of_le two_pos (hN2 v)
  have hNC : ∀ v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}, (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ)) ≠ 0 :=
    fun v => by exact_mod_cast (hNpos v).ne'

  have hNκ : ∀ v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S},
      ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ κ ≤ ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ κ' :=
    fun v => Real.rpow_le_rpow_of_exponent_le (by linarith [hN2 v]) (le_max_left _ _)
  have hNκ1 : ∀ v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}, (1 : ℝ) ≤ ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ κ' :=
    fun v => Real.one_le_rpow (by linarith [hN2 v]) (le_max_right _ _)
  have hroot : ∀ v, ‖α v‖ ≤ 2 * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ κ' ∧
      ‖β v‖ ≤ 2 * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ κ' ∧
      ‖γ v‖ ≤ 2 * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ κ' ∧
      ‖δ v‖ ≤ 2 * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ κ' := by
    intro v
    obtain ⟨ha, hb, ha', hb'⟩ := hbd v
    have hm : max 1 (‖a v‖ + ‖b v‖) ≤ 2 * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ κ' :=
      max_le (by linarith [hNκ1 v]) (by linarith [hNκ v])
    have hm' : max 1 (‖a' v‖ + ‖b' v‖) ≤ 2 * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ κ' :=
      max_le (by linarith [hNκ1 v]) (by linarith [hNκ v])
    refine ⟨(norm_root_le (hαβ v).1 (hαβ v).2).trans hm, ?_, (norm_root_le (hγδ v).1 (hγδ v).2).trans hm', ?_⟩
    · have h1 : β v + α v = a v := by rw [add_comm]; exact (hαβ v).1
      have h2 : β v * α v = b v := by rw [mul_comm]; exact (hαβ v).2
      exact (norm_root_le h1 h2).trans hm
    · have h1 : δ v + γ v = a' v := by rw [add_comm]; exact (hγδ v).1
      have h2 : δ v * γ v = b' v := by rw [mul_comm]; exact (hγδ v).2
      exact (norm_root_le h1 h2).trans hm'

  set w : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} → ℂ := fun v =>
    (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ)) ^ (-(t : ℂ)) with hw
  have hwnorm : ∀ v, ‖w v‖ = (((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ t)⁻¹ := by
    intro v
    simp only [hw]
    rw [Complex.norm_natCast_cpow_of_pos (by exact_mod_cast (hNpos v)), Complex.neg_re, Complex.ofReal_re,
      Real.rpow_neg (hNpos v).le]
  have hzbound : ∀ (x y : ℂ) (v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}),
      ‖x‖ ≤ 2 * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ κ' → ‖y‖ ≤ 2 * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ κ' →
        ‖x * y * w v‖ ≤ 1 := by
    intro x y v hx hy
    have hN := hN2 v
    have hp : 0 < ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ κ' := by positivity
    rw [norm_mul, norm_mul, hwnorm v, ht]
    have hsplit : ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ (2 * κ' + 2) =
        (((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ κ') ^ 2 * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ 2 := by
      rw [show (2 * κ' + 2 : ℝ) = κ' * 2 + 2 by ring, Real.rpow_add (hNpos v), Real.rpow_mul (hNpos v).le,
        Real.rpow_two, Real.rpow_two]
    rw [hsplit]
    have h4 : ‖x‖ * ‖y‖ ≤ 4 * (((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ κ') ^ 2 := by
      nlinarith [norm_nonneg x, norm_nonneg y]
    have hNsq : (4 : ℝ) ≤ ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ 2 := by nlinarith
    rw [mul_inv_le_iff₀ (by positivity), one_mul]
    nlinarith [h4, hNsq, hp]
  set z₁ : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} → ℂ := fun v => α v * γ v * w v with hz₁
  set z₂ : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} → ℂ := fun v => α v * δ v * w v with hz₂
  set z₃ : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} → ℂ := fun v => β v * γ v * w v with hz₃
  set z₄ : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} → ℂ := fun v => β v * δ v * w v with hz₄
  have hz₁b : ∀ v, ‖z₁ v‖ ≤ 1 := fun v => hzbound _ _ v (hroot v).1 (hroot v).2.2.1
  have hz₂b : ∀ v, ‖z₂ v‖ ≤ 1 := fun v => hzbound _ _ v (hroot v).1 (hroot v).2.2.2
  have hz₃b : ∀ v, ‖z₃ v‖ ≤ 1 := fun v => hzbound _ _ v (hroot v).2.1 (hroot v).2.2.1
  have hz₄b : ∀ v, ‖z₄ v‖ ≤ 1 := fun v => hzbound _ _ v (hroot v).2.1 (hroot v).2.2.2
  obtain ⟨hm₁, hd₁, hn₁⟩ :=
    NumberField.ZetaEuler.multipliable_differentiableOn_tprod_ne_zero_eulerProduct_of_norm_le_one K S z₁ hz₁b
  obtain ⟨hm₂, hd₂, hn₂⟩ :=
    NumberField.ZetaEuler.multipliable_differentiableOn_tprod_ne_zero_eulerProduct_of_norm_le_one K S z₂ hz₂b
  obtain ⟨hm₃, hd₃, hn₃⟩ :=
    NumberField.ZetaEuler.multipliable_differentiableOn_tprod_ne_zero_eulerProduct_of_norm_le_one K S z₃ hz₃b
  obtain ⟨hm₄, hd₄, hn₄⟩ :=
    NumberField.ZetaEuler.multipliable_differentiableOn_tprod_ne_zero_eulerProduct_of_norm_le_one K S z₄ hz₄b

  have hfac : ∀ (s : ℂ) (v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}),
      ((LanglandsTunnell.RankinSelberg.rsEulerPoly (a v) (b v) (a' v) (b' v) 0).eval
          (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹ =
        (1 - z₁ v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(s - t)))⁻¹ *
        (1 - z₂ v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(s - t)))⁻¹ *
        (1 - z₃ v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(s - t)))⁻¹ *
        (1 - z₄ v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(s - t)))⁻¹ := by
    intro s v
    have hxw : ∀ x y : ℂ, x * y * w v * (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(s - t))) =
        x * y * (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)) := by
      intro x y
      simp only [hw]
      rw [mul_assoc (x * y), ← Complex.cpow_add _ _ (hNC v)]
      congr 2
      ring
    rw [← (hαβ v).1, ← (hαβ v).2, ← (hγδ v).1, ← (hγδ v).2, eval_rsEulerPoly_eq, hz₁, hz₂, hz₃, hz₄]
    simp only [hxw]
    rw [mul_inv, mul_inv, mul_inv]
  refine ⟨t + 1, fun s hs => ?_, ?_, fun s hs => ?_⟩
  ·
    have hs' : 1 < (s - t).re := by rw [Complex.sub_re, Complex.ofReal_re]; linarith
    have h := ((hm₁ _ hs').mul (hm₂ _ hs')).mul (hm₃ _ hs') |>.mul (hm₄ _ hs')
    refine h.congr fun v => ?_
    rw [hfac s v]
  ·
    have hshift : ∀ s : ℂ, s ∈ {s : ℂ | t + 1 < s.re} → s - t ∈ {s : ℂ | 1 < s.re} := by
      intro s hs
      simp only [Set.mem_ofPred_eq, Complex.sub_re, Complex.ofReal_re] at hs ⊢
      linarith
    have hsub : DifferentiableOn ℂ (fun s : ℂ => s - (t : ℂ)) {s : ℂ | t + 1 < s.re} :=
      (differentiable_id.sub_const _).differentiableOn
    have hD := (((hd₁.comp hsub hshift).mul (hd₂.comp hsub hshift)).mul (hd₃.comp hsub hshift)).mul
      (hd₄.comp hsub hshift)
    refine hD.congr fun s hs => ?_
    have hs' : 1 < (s - t).re := hshift s hs
    simp only [Pi.mul_apply, Function.comp_apply]
    rw [← (hm₁ _ hs').tprod_mul (hm₂ _ hs'), ← ((hm₁ _ hs').mul (hm₂ _ hs')).tprod_mul (hm₃ _ hs'),
      ← (((hm₁ _ hs').mul (hm₂ _ hs')).mul (hm₃ _ hs')).tprod_mul (hm₄ _ hs')]
    exact tprod_congr fun v => hfac s v
  ·
    have hs' : 1 < (s - t).re := by rw [Complex.sub_re, Complex.ofReal_re]; linarith
    rw [tprod_congr fun v => hfac s v, (((hm₁ _ hs').mul (hm₂ _ hs')).mul (hm₃ _ hs')).tprod_mul (hm₄ _ hs'),
      ((hm₁ _ hs').mul (hm₂ _ hs')).tprod_mul (hm₃ _ hs'), (hm₁ _ hs').tprod_mul (hm₂ _ hs')]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (hn₁ _ hs') (hn₂ _ hs')) (hn₃ _ hs')) (hn₄ _ hs')

/-- Convergence of the Rankin–Selberg `GL₂ × GL₂` Euler product: the row's statement, the pin's own
specialization of `main` to the row's name. -/
theorem exists_multipliable_differentiableOn_tprod_inv_eval_rsEulerPoly_of_norm_le_rpow
    (K : Type) [Field K] [NumberField K] (S : Finset (HeightOneSpectrum (𝓞 K)))
    (a b a' b' : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} → ℂ) (κ : ℝ)
    (hbd : ∀ v, ‖a v‖ ≤ ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ κ ∧ ‖b v‖ ≤ ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ κ ∧
      ‖a' v‖ ≤ ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ κ ∧ ‖b' v‖ ≤ ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ κ) :
    ∃ σ₀ : ℝ,
      (∀ s : ℂ, σ₀ < s.re →
        Multipliable (fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} =>
          ((LanglandsTunnell.RankinSelberg.rsEulerPoly (a v) (b v) (a' v) (b' v) 0).eval
            (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹)) ∧
      DifferentiableOn ℂ (fun s : ℂ => ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S},
          ((LanglandsTunnell.RankinSelberg.rsEulerPoly (a v) (b v) (a' v) (b' v) 0).eval
            (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) {s : ℂ | σ₀ < s.re} ∧
      (∀ s : ℂ, σ₀ < s.re →
        (∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S},
          ((LanglandsTunnell.RankinSelberg.rsEulerPoly (a v) (b v) (a' v) (b' v) 0).eval
            (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) ≠ 0) :=
  main K S a b a' b' κ hbd

end LanglandsTunnell.RankinSelberg
