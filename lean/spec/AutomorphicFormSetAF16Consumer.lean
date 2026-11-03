/-
  SET-AF16 consumer: the three compositions this set's headlines are for.

  **Zone 1 (order A) — regularity first, then equality.** The set's two `AutomorphicForm` headlines
  say the same thing from two sides. `continuousOn_of_forall_apply_borel_mul_eq_of_continuousOn`
  turns the pointwise Borel form `φ (b * k) = Φ b k` — continuous in `(b, k)` on Borel × maximal
  compact — into continuity of `φ` on the whole group; `IsInducedSection.eq_of_eqOn_maximalCompact`
  turns agreement with `φ'` on the maximal compact into equality of the two functions. Composed: two
  induced sections whose common Borel form is continuous in `(b, k)` and which agree on the maximal
  compact are *equal* — and the first headline is what makes the word "continuous" reach the whole
  group. (`Unit` is the index space `X` the first headline allows; the section is indexed trivially,
  so `X = Unit` and `U = univ` are exactly "a single section".)

  **Zone 2 (order B) — the decomposition at `n = 1` is a single product.** The span headline gives
  `φ s g = ∑ i : Fin n, c i s * ψ i s g` with `ψ i` flat on the integral row-isometry subgroup.
  Reading it at `n = 1` collapses the sum to its one term: `φ s = c 0 s * ψ 0 s`, with `ψ 0` still
  constant in its `K`-argument — the shape the cuspidal analysis consumes.

  **Zone 3 (order C) — the `diagOne` reduction meets Siegel compactness.** The first headline
  produces `(t, k)` with `k` in `maximalCompactAt F S`, `t` trivial outside `S` and `W (diagOne t * k)`
  non-zero; the second places the *translate* `diagOne t` by a `k`-right-translate in a compact set
  `Ω` at a height comparable to `archHeight (glArch (diagOne t))`, uniformly in the integral factor.
  Composed: the non-vanishing point can be written `b * ω` with `ω ∈ Ω` compact and `b` of bounded
  `hgt` — the Siegel-set reading the centre-cut estimates quantify over.
-/
import FLTForHuman.AutomorphicForm.Adelic.InducedSectionKRegular
import FLTForHuman.AutomorphicForm.Adelic.InducedSectionSpan
import FLTForHuman.AutomorphicForm.Adelic.MaximalCompactReductions

set_option autoImplicit false

noncomputable section

open MeasureTheory
open NumberField NumberField.AdelicLevel NumberField.InfinitePlace NumberField.AdelicHeight
open IsDedekindDomain AutomorphicForm AutomorphicForm.WindowedSiegel
open scoped NNReal

namespace AutomorphicForm
namespace LocalIntertwining

/-! ### Zone 1 (order A) — an induced section is determined by its maximal compact -/

/-- **Zone 1.** If the pointwise Borel form `Φ` of `φ` is continuous in `(b, k)` on
`borel × maximalCompact` and `φ'` is an induced section agreeing with `φ` on the maximal compact,
then `φ` is continuous and `φ = φ'`. -/
example (F : Type) [Field F] [NumberField F]
    (χ₁ χ₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (φ φ' : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : IsInducedSection (𝓞 F) F χ₁ χ₂ φ) (hφ' : IsInducedSection (𝓞 F) F χ₁ χ₂ φ')
    (Φ : AdelicGL2 (𝓞 F) F → AdelicGL2 (𝓞 F) F → ℂ)
    (hΦ : ContinuousOn (fun p : Unit × AdelicGL2 (𝓞 F) F × AdelicGL2 (𝓞 F) F => Φ p.2.1 p.2.2)
      (Set.univ ×ˢ ((adelicBorel (𝓞 F) F : Set (AdelicGL2 (𝓞 F) F)) ×ˢ
        {k | glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F ∧
          ∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))})))
    (hlaw : ∀ b ∈ adelicBorel (𝓞 F) F, ∀ k : AdelicGL2 (𝓞 F) F,
      glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F →
      (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) →
      φ (b * k) = Φ b k)
    (h : ∀ k : AdelicGL2 (𝓞 F) F, glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F →
      (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) → φ k = φ' k) :
    Continuous φ ∧ φ = φ' := by
  have hcont : ContinuousOn (fun p : Unit × AdelicGL2 (𝓞 F) F => φ p.2)
      (Set.univ ×ˢ (Set.univ : Set (AdelicGL2 (𝓞 F) F))) :=
    _root_.AutomorphicForm.continuousOn_of_forall_apply_borel_mul_eq_of_continuousOn F
      Set.univ isOpen_univ (fun _ : Unit => φ) (fun (_ : Unit) b k => Φ b k) hΦ
      (fun (_ : Unit) _ b hb k h1 h2 => hlaw b hb k h1 h2)
  have hcontu : Continuous (fun p : Unit × AdelicGL2 (𝓞 F) F => φ p.2) :=
    continuousOn_univ.mp
      (hcont.mono fun p _ => Set.mem_prod.mpr ⟨Set.mem_univ _, Set.mem_univ _⟩)
  have hpair : Continuous (fun g : AdelicGL2 (𝓞 F) F => ((), g)) :=
    continuous_const.prodMk continuous_id
  refine ⟨?_, IsInducedSection.eq_of_eqOn_maximalCompact F χ₁ χ₂ φ φ' hφ hφ' h⟩
  simpa [Function.comp_def] using hcontu.comp hpair

/-! ### Zone 2 (order B) — the decomposition at `n = 1` -/

/-- **Zone 2.** A differentiable family of flat sections is a finite sum of flat `K`-constant
sections; at `n = 1` that sum is the single product `φ s = c 0 s * ψ 0 s`, and `ψ 0` is still
constant in its `K`-argument on the integral row-isometry subgroup. -/
example (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) (φ s))
      (_hφK : ∀ s, IsArchKFinite F (φ s))
      (_hφf : ∀ s, IsKfSmooth F (φ s))
      (_hφjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φ p.1 p.2))
      (_hφhol : ∀ g, Differentiable ℂ (fun s => φ s g)),
    ∃ (n : ℕ) (c : Fin n → ℂ → ℂ) (ψ : Fin n → ℂ → AdelicGL2 (𝓞 F) F → ℂ),
      (∀ i s, IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) (ψ i s))
      ∧ (∀ (i : Fin n) (s s' : ℂ) (k : AdelicGL2 (𝓞 F) F),
          glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F →
          (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) →
          ψ i s k = ψ i s' k)
      ∧ (∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F), φ s g = ∑ i, c i s * ψ i s g)
      ∧ (n = 1 → ∃ (c₀ : ℂ → ℂ) (ψ₀ : ℂ → AdelicGL2 (𝓞 F) F → ℂ),
          (∀ (s s' : ℂ) (k : AdelicGL2 (𝓞 F) F),
            glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F →
            (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) →
            ψ₀ s k = ψ₀ s' k)
          ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F), φ s g = c₀ s * ψ₀ s g) := by
  intro α hα μ ν φ hφ hφK hφf hφjc hφhol
  obtain ⟨n, c, ψ, _hc, hind, _hK, _hf, _hcont, _hhol, hconst, hsum⟩ :=
    _root_.AutomorphicForm.exists_flat_isInducedSection_sum_eq_of_differentiable_family
      F hα μ ν φ hφ hφK hφf hφjc hφhol
  refine ⟨n, c, ψ, hind, hconst, hsum, fun hn => ?_⟩
  subst hn
  exact ⟨c 0, ψ 0, fun s s' k h1 h2 => hconst 0 s s' k h1 h2,
    fun s g => by rw [hsum s g, Fin.sum_univ_one]⟩

/-! ### Zone 3 (order C) — the `diagOne` reduction, placed in a compact Siegel set -/

/-- **Zone 3.** A Whittaker function non-zero at `g₀` is non-zero at `diagOne t * k` for some `t`
trivial outside `S` and `k ∈ maximalCompactAt F S`; and that point is `b * ω` with `ω` in a compact
set `Ω`, with `hgt b` bounded above and below by `archHeight (glArch (diagOne t))`. -/
example (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (W : AdelicGL2 (𝓞 F) F → ℂ)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (ω : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (hN : ∀ (u : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F), W (unipotentGL2 u * g) = ψ u * W g)
    (hZ : ∀ (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F),
      W (centralScalar (𝓞 F) F z * g) = ((ω z : ℂˣ) : ℂ) * W g)
    (g₀ : AdelicGL2 (𝓞 F) F)
    (hg₀ : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → ∀ i j : Fin 2,
      ((g₀ : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 v =
        ((1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 v)
    (hW : W g₀ ≠ 0) :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∃ (t : (AdeleRing (𝓞 F) F)ˣ) (k : AdelicGL2 (𝓞 F) F) (k₁ k₂ : ℝ)
      (Ω : Set (AdelicGL2 (𝓞 F) F)),
      k ∈ maximalCompactAt F S ∧
      (∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → ((t : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v = 1) ∧
      W (diagOne t * k) ≠ 0 ∧
      0 < k₁ ∧ k₁ ≤ k₂ ∧ IsCompact Ω ∧
      ∃ (b : ↥(adelicBorel (𝓞 F) F)) (u : AdelicGL2 (𝓞 F) F), u ∈ Ω ∧
        k * diagOne t = (b : AdelicGL2 (𝓞 F) F) * u ∧
        k₁ ≤ ((α (borelDiagFst b) : ℝˣ) : ℝ) / ((α (borelDiagSnd b) : ℝˣ) : ℝ) ∧
        ((α (borelDiagFst b) : ℝˣ) : ℝ) / ((α (borelDiagSnd b) : ℝˣ) : ℝ) ≤ k₂ := by
  intro α
  obtain ⟨t, k, hkK, htS, hWk⟩ :=
    _root_.AutomorphicForm.exists_mem_maximalCompactAt_apply_diagOne_mul_ne_zero_of_apply_ne_zero
      F S W ψ ω hN hZ g₀ hg₀ hW
  obtain ⟨k₁, k₂, Ω, hk1, hk12, hΩ, hΩmem⟩ :=
    _root_.AutomorphicForm.exists_isCompact_forall_mul_eq_borel_mul_archHeight_le_of_glFin_mem_finiteIntegralGL2
      F (diagOne t)
  obtain ⟨b, u, hu, hdecomp, hlow, hhigh⟩ := hΩmem k hkK.1.1
  have harch1 : archHeight F (glArch (𝓞 F) F k) = 1 := by
    have h := archHeight_mul_rowIsometry F (1 : GL (Fin 2) (InfiniteAdeleRing F)) hkK.1.2
    rwa [one_mul, archHeight_one] at h
  rw [harch1, mul_one] at hlow hhigh
  exact ⟨t, k, k₁, k₂, Ω, hkK, htS, hWk, hk1, hk12, hΩ, b, u, hu, hdecomp, hlow, hhigh⟩

end LocalIntertwining
end AutomorphicForm
