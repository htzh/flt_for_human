/-
  Consumer for `SET-AF62` §1 (row C) / §2: the archimedean × finite factorization of the adelic
  integral.

  The headline `NumberField.AdelicHaar.exists_integral_glArch_mul_glFin_eq_mul_integral_mul_integral`
  is *applied* below — the compositions are real terms, not `#check`s.  The Haar measures on the two
  `GL₂` factors are arbitrary data with their hypotheses (they cannot be instantiated concretely: a
  Haar measure is a datum, and a general number field's places are a hypothesis), so both examples
  take them as arguments.
-/
import FLTForHuman.NumberTheory.AdelicHaar.ArchFiniteFactorization

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain MeasureTheory NumberField.AdelicHaar NumberField.AdelicLevel
open scoped NNReal Pointwise

namespace NumberFieldSetAF62BConsumer

/-- The factorization, spent: for any pair of test functions whose archimedean integral vanishes,
the adelic integral of the product `Φ ∘ glArch * Ψ ∘ glFin` vanishes, whatever the finite factor
does.  The scalar `c` produced by the headline is consumed and then killed by the vanishing
archimedean integral. -/
example (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (GL (Fin 2) (InfiniteAdeleRing K))] [BorelSpace (GL (Fin 2) (InfiniteAdeleRing K))]
    [MeasurableSpace (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))]
    [BorelSpace (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))]
    (μa : Measure (GL (Fin 2) (InfiniteAdeleRing K))) [μa.IsHaarMeasure] [μa.Regular]
    (μf : Measure (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))) [μf.IsHaarMeasure] [μf.Regular]
    (Φ : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) (Ψ : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ)
    (hΦ : ∫ a, Φ a ∂μa = 0) :
    (letI := glBorel (Fin 2) (𝓞 K) K
     ∫ x, Φ (glArch (𝓞 K) K x) * Ψ (glFin (𝓞 K) K x) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) = 0 := by
  obtain ⟨c, _, h⟩ :=
    NumberField.AdelicHaar.exists_integral_glArch_mul_glFin_eq_mul_integral_mul_integral K μa μf
  rw [h Φ Ψ, hΦ, zero_mul, mul_zero]

/-- The same factorization at the concrete base `K = ℚ`, consumed at the constant test function:
the adelic integral of `1` is the scalar times the product of the two local total masses. -/
example
    [MeasurableSpace (GL (Fin 2) (InfiniteAdeleRing ℚ))] [BorelSpace (GL (Fin 2) (InfiniteAdeleRing ℚ))]
    [MeasurableSpace (GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ))]
    [BorelSpace (GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ))]
    (μa : Measure (GL (Fin 2) (InfiniteAdeleRing ℚ))) [μa.IsHaarMeasure] [μa.Regular]
    (μf : Measure (GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ))) [μf.IsHaarMeasure] [μf.Regular] :
    ∃ c : ℝ≥0, 0 < c ∧
      (letI := glBorel (Fin 2) (𝓞 ℚ) ℚ
       ∫ _x, (1 : ℂ) * 1 ∂(adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ))
        = (c : ℂ) * ((∫ _a, (1 : ℂ) ∂μa) * ∫ _b, (1 : ℂ) ∂μf) := by
  obtain ⟨c, hc, h⟩ :=
    NumberField.AdelicHaar.exists_integral_glArch_mul_glFin_eq_mul_integral_mul_integral ℚ μa μf
  exact ⟨c, hc, h (fun _ => 1) (fun _ => 1)⟩

end NumberFieldSetAF62BConsumer
