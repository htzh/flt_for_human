/-
  SET-AF80B consumer: boundedness and convergence of the Weyl shift, spent at `F = ℚ`.

  **The row.** `FLTForHuman/AutomorphicForm/Adelic/WeylIntegrable/ShiftConvergence.lean` carries the
  pin's `solution` (`S_…:454–470`) as
  `AutomorphicForm.LocalIntertwining.bounded_and_tendsto_integral_weylShift_sub_integral_smoothAtom_adicCompletion`:
  for a smooth atom `a` at depth `m` on a completed nonarchimedean place, the integral `∫ a σ`
  is bounded on `1/2 < σ ≤ 1` and the *Weyl shift* of the atom,
  `∫ x, |modulus x| ^ (-(2σ+1)) • a σ x⁻¹`, differs from it by a quantity tending to `0` as
  `σ → 1/2⁺`.

  **What is concrete here.** Everything the row leaves abstract:

  * `F = ℚ`; `v = vTwo`, the height-one prime `(2)` of `𝓞 ℚ` (primality transported from
    `Int.prime_two` along `Rat.ringOfIntegersEquiv`), so `vTwo.adicCompletion ℚ` is `ℚ₂`;
  * `μ = μTwo = Measure.addHaar`, the chosen additive Haar measure, with the `BorelSpace`
    structure supplied locally (mathlib registers none for the completion);
  * `m = 1` and the two atoms: `atomA` is the indicator of the completed integer ring `𝓞̂`
    (locally constant on `𝓞̂` at any depth — the hypothesis only quantifies inside `𝓞̂`), and
    `atomB` is the constant `1` (trivially invariant under `y - x ∈ ϖ𝓞̂`).  The atom
    `atom σ = a σ` is then the pin's own shape: `atomA` on `𝓞̂`, and
    `|modulus y| ^ (-(2σ+1)) • atomB y⁻¹` off it.

  **The readings.** `row` is the headline applied to this data; the zones read its two halves:

  * Zone 1 — the bound, at `σ = 1` and at `σ = 3/4` (both in `(1/2, 1]`): some real `C` bounds
    `‖∫ x, atom σ x ∂μTwo‖`.
  * Zone 2 — the limit as an eventual statement near `1/2⁺`: eventually the shifted integral minus
    the unshifted one has norm `< 1`.
  * Zone 3 — the limit read along the explicit sequence `σ n = 1/2 + 1/(n+1)`, which tends to `1/2`
    from above (`sigmaSeq_tendsto`); composing gives `Tendsto (fun n => weylDiff (σ n)) atTop (𝓝 0)`.
    This is the form the pin's consumers use: the shift parameter walks a sequence leaving every
    set that keeps away from the boundary point `1/2`.

  The pin's "shift" in this row is the inversion `x ↦ x⁻¹` weighted by the modulus, not a family of
  translations, so what walks off to infinity is the exponent `σ ↓ 1/2` and not a unipotent
  parameter; Zone 3 is that walk made explicit.

  `spec/` is outside every Lake library, so this file is checked by
  `lake env lean spec/AutomorphicFormSetAF80BConsumer.lean` and never enters the build.
-/
import FLTForHuman.AutomorphicForm.Adelic.WeylIntegrable.ShiftConvergence

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField IsDedekindDomain
  IsDedekindDomain.HeightOneSpectrum Topology Filter
open scoped NNReal ENNReal Pointwise

namespace AutomorphicFormSetAF80BConsumer

/-! ### The place `v = 2` of `ℚ` -/

/-- The ideal `(2) ⊆ 𝓞 ℚ` is prime: it is the image of the prime `(2) ⊆ ℤ` under the ring
equivalence `𝓞 ℚ ≃+* ℤ`. -/
theorem span_two_isPrime : (Ideal.span ({(2 : 𝓞 ℚ)} : Set (𝓞 ℚ))).IsPrime := by
  have htwo : (Ideal.span ({(2 : ℤ)} : Set ℤ)).IsPrime :=
    (Ideal.span_singleton_prime (p := (2 : ℤ)) (by norm_num)).mpr Int.prime_two
  have hmap : Ideal.map (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ)
        (Ideal.span ({(2 : ℤ)} : Set ℤ))
      = Ideal.span ({(2 : 𝓞 ℚ)} : Set (𝓞 ℚ)) := by
    rw [Ideal.map_span, Set.image_singleton]
    norm_num
  rw [← hmap]
  refine Ideal.map_isPrime_of_surjective (I := Ideal.span ({(2 : ℤ)} : Set ℤ))
    Rat.ringOfIntegersEquiv.symm.surjective ?_
  rw [(RingHom.injective_iff_ker_eq_bot _).mp Rat.ringOfIntegersEquiv.symm.injective]
  exact bot_le

/-- `(2) ≠ 0` in `𝓞 ℚ`. -/
theorem span_two_ne_bot : Ideal.span ({(2 : 𝓞 ℚ)} : Set (𝓞 ℚ)) ≠ ⊥ := by
  rw [Ne, Ideal.span_singleton_eq_bot]
  norm_num

/-- The place `v = 2` of `ℚ`: the height-one prime `(2)` of `𝓞 ℚ`. -/
def vTwo : HeightOneSpectrum (𝓞 ℚ) :=
  ⟨Ideal.span ({(2 : 𝓞 ℚ)} : Set (𝓞 ℚ)), span_two_isPrime, span_two_ne_bot⟩

/-! ### `ℚ₂` as a measure space with a Haar measure -/

instance : MeasurableSpace (vTwo.adicCompletion ℚ) := borel _

instance : BorelSpace (vTwo.adicCompletion ℚ) := ⟨rfl⟩

/-- The chosen additive Haar measure on `ℚ₂`; an `abbrev` so that instance search sees its
`IsAddHaarMeasure` instance through it. -/
abbrev μTwo : Measure (vTwo.adicCompletion ℚ) := Measure.addHaar

instance : μTwo.IsAddHaarMeasure := inferInstance

/-! ### The concrete smooth atom at depth `m = 1` -/

/-- The completed integer ring of `ℚ₂`, the compact set the atom is supported on. -/
private abbrev O : Set (vTwo.adicCompletion ℚ) :=
  (vTwo.adicCompletionIntegers ℚ : Set (vTwo.adicCompletion ℚ))

/-- The `𝓞̂`-part of the atom: the indicator of the completed integer ring. -/
private def atomA : vTwo.adicCompletion ℚ → ℂ := O.indicator (fun _ => (1 : ℂ))

/-- The off-`𝓞̂` part of the atom: the constant `1`, invariant under `y - x ∈ ϖ𝓞̂`. -/
private def atomB : vTwo.adicCompletion ℚ → ℂ := fun _ => (1 : ℂ)

/-- `atomA` is locally constant on `𝓞̂` at depth `m = 1`: the hypothesis quantifies only inside
`𝓞̂`, where the indicator is constantly `1`. -/
private theorem atomA_smooth :
    ∀ x ∈ O, ∀ y ∈ O, Valued.v (y - x) ≤ Multiplicative.ofAdd (-(1 : ℤ)) → atomA y = atomA x := by
  intro x hx y hy _
  simp only [atomA, Set.indicator_of_mem hx, Set.indicator_of_mem hy]

/-- `atomB = 1` is invariant under any shift. -/
private theorem atomB_smooth :
    ∀ x y : vTwo.adicCompletion ℚ, Valued.v (y - x) ≤ Multiplicative.ofAdd (-(1 : ℤ)) →
      atomB y = atomB x :=
  fun _ _ _ => rfl

/-- The pin's smooth atom at the concrete data: `atomA` on `𝓞̂` and
`|modulus y| ^ (-(2σ+1)) • atomB y⁻¹` off it. -/
private def atom (σ : ℝ) : vTwo.adicCompletion ℚ → ℂ := fun x =>
  O.indicator atomA x
    + Oᶜ.indicator
        (fun y =>
          (((LanglandsTunnell.TateLocal.modulus y : ℝ≥0) : ℝ) : ℂ) ^ (-(2 * (σ : ℂ) + 1))
            * atomB y⁻¹) x

/-- The Weyl shift minus the unshifted integral: the quantity the row sends to `0`. -/
private def weylDiff (σ : ℝ) : ℂ :=
  (∫ x,
      (((LanglandsTunnell.TateLocal.modulus x : ℝ≥0) : ℝ) : ℂ) ^ (-(2 * (σ : ℂ) + 1))
        * atom σ x⁻¹ ∂μTwo)
    - ∫ x, atom σ x ∂μTwo

/-- **The row at the concrete data.** The headline instantiated at `F = ℚ`, `v = vTwo`,
`μ = μTwo`, `m = 1` and the two atoms above. -/
private theorem row :
    (∃ C : ℝ, ∀ σ : ℝ, 1 / 2 < σ → σ ≤ 1 → ‖∫ x, atom σ x ∂μTwo‖ ≤ C) ∧
      Tendsto weylDiff (𝓝[>] (1 / 2 : ℝ)) (𝓝 0) :=
  AutomorphicForm.LocalIntertwining.bounded_and_tendsto_integral_weylShift_sub_integral_smoothAtom_adicCompletion
    ℚ vTwo μTwo 1 le_rfl atomA atomB atomA_smooth atomB_smooth

/-! ### Zone 1 — the bound -/

/-- **Zone 1a.** At `σ = 1` the bound is a real number. -/
theorem bound_at_one : ∃ C : ℝ, ‖∫ x, atom 1 x ∂μTwo‖ ≤ C := by
  obtain ⟨C, hC⟩ := row.1
  exact ⟨C, hC 1 (by norm_num) le_rfl⟩

/-- **Zone 1b.** At `σ = 3/4` the same `C` bounds the integral. -/
theorem bound_at_three_quarters : ∃ C : ℝ, ‖∫ x, atom (3 / 4) x ∂μTwo‖ ≤ C := by
  obtain ⟨C, hC⟩ := row.1
  exact ⟨C, hC (3 / 4) (by norm_num) (by norm_num)⟩

/-! ### Zone 2 — the limit as an eventual statement -/

/-- **Zone 2.** Eventually near `1/2⁺` the difference of the two integrals has norm `< 1`. -/
theorem limit_eventually_close :
    ∀ᶠ σ : ℝ in 𝓝[>] (1 / 2 : ℝ), ‖weylDiff σ‖ < 1 := by
  have h := row.2.eventually (Metric.ball_mem_nhds (0 : ℂ) zero_lt_one)
  filter_upwards [h] with σ hσ
  simpa only [Metric.mem_ball, dist_zero_right] using hσ

/-! ### Zone 3 — the limit along an explicit sequence -/

/-- The sequence `σ n = 1/2 + 1/(n+1)`: the shift parameter walking to the boundary `1/2`. -/
private def sigmaSeq (n : ℕ) : ℝ := 1 / 2 + 1 / ((n : ℝ) + 1)

/-- **Zone 3a.** `σ n → 1/2` from above. -/
theorem sigmaSeq_tendsto : Tendsto sigmaSeq atTop (𝓝[>] (1 / 2 : ℝ)) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, ?_⟩
  · have h : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h' : Tendsto (fun n : ℕ => (1 / 2 : ℝ) + 1 / ((n : ℝ) + 1)) atTop (𝓝 (1 / 2)) := by
      simpa only [add_zero] using (tendsto_const_nhds (x := (1 / 2 : ℝ))).add h
    exact h'
  · filter_upwards with n
    simp only [Set.mem_Ioi, sigmaSeq]
    have h : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith

/-- **Zone 3b.** Consequently the difference tends to `0` along `σ n`. -/
theorem limit_along_sigmaSeq : Tendsto (fun n : ℕ => weylDiff (sigmaSeq n)) atTop (𝓝 0) :=
  row.2.comp sigmaSeq_tendsto

end AutomorphicFormSetAF80BConsumer
