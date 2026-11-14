/-
  Cross-module wire test for the isotypic convolution projection (`AF74A`).

  A `spec/` probe, not a library module. One executed zone: the headline
  `MeasureTheory.exists_continuous_convolution_self_eq_forall_integral_smul_isotypic` at the
  **trivial compact group** `K = Unit`, with `ρ` the one-dimensional trivial representation,
  `μ` the normalised Haar measure `haarMeasure ⊤`, and `π` the trivial representation of `Unit`
  on `ℂ`. The zone reads the *idempotence* clause of the headline at the concrete vector
  `1 : ℂ`: the averaging operator `A v = e () • v` satisfies `A (A 1) = A 1`.

  Every zone is a real composition — no `#check` — so deleting the module (or leaving a hole
  in it) breaks this file. The instantiation is the degenerate case in which the pin's whole
  averaging operator must collapse to the scalar `e ()` times the identity, because the
  trivial group has a single element and its Haar measure is a point mass: the two
  convolution integrals of the headline are evaluations at `()`.
-/
import FLTForHuman.MeasureTheory.IsotypicConvolution

open MeasureTheory
open scoped ComplexConjugate

namespace IsotypicConvolutionConsumer

noncomputable section

/-- The normalised Haar measure of the trivial compact group is a probability measure: it is
`haarMeasure ⊤`, whose total mass is `⊤`'s mass, i.e. `1`. -/
private instance isProbabilityMeasure_haarMeasure_top :
    IsProbabilityMeasure
      (Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts Unit)) :=
  ⟨by
    simpa using
      Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts Unit))⟩

/-- The trivial group's one-dimensional trivial representation, as a matrix-valued monoid
homomorphism: the pin's `ρ` at `n = 1`. -/
private def trivMat : Unit →* Matrix (Fin 1) (Fin 1) ℂ := 1

/-- The trivial representation of the trivial group on `ℂ`: the pin's `π`. -/
private def trivRep : Unit →* (ℂ →L[ℂ] ℂ) := 1

/-! ### Zone — the idempotence clause at the trivial group, read at `1 : ℂ` -/

/-- The headline of `IsotypicConvolution` at `K = Unit`, `ρ = trivMat`, `μ = haarMeasure ⊤`,
`π = trivRep`, `H = ℂ`: the projection `A v = e () • v` is idempotent, as read at the vector
`1`. -/
theorem exists_idempotent_at_one : ∃ A : ℂ →L[ℂ] ℂ, A (A 1) = A 1 := by
  obtain ⟨e, -, -, -, -, hmain⟩ :=
    MeasureTheory.exists_continuous_convolution_self_eq_forall_integral_smul_isotypic
      (K := Unit)
      (μ := Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts Unit))
      (n := 1) (ρ := trivMat) continuous_const
  -- the averaging operator of the headline, at the trivial group: scalar multiplication by
  -- `e ()`, since `Unit` has one element and `π` is trivial
  let A : ℂ →L[ℂ] ℂ := (e () : ℂ) • ContinuousLinearMap.id ℂ ℂ
  have hA : ∀ v : ℂ, A v = ∫ k : Unit, (e k) • (trivRep k) v
      ∂(Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts Unit)) := by
    intro v
    have hpt : ∀ k : Unit, (e k) • (trivRep k) v = e () • v := by
      intro k
      rw [Subsingleton.elim k ()]
      simp [trivRep]
    simp only [hpt]
    rw [integral_const, probReal_univ, one_smul]
    simp [A]
  obtain ⟨hidem, -, -⟩ :=
    hmain ℂ trivRep (fun k v => by simp [trivRep]) (fun v => by
      have h : (fun k : Unit => (trivRep k) v) = fun _ => v := by
        funext k
        simp [trivRep]
      rw [h]
      exact continuous_const) A hA
  refine ⟨A, ?_⟩
  have h := congrArg (fun f : ℂ →L[ℂ] ℂ => f 1) hidem
  simpa [ContinuousLinearMap.comp_apply] using h

end

end IsotypicConvolutionConsumer
