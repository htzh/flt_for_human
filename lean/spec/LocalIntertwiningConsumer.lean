/-
  Consumer for the `AutomorphicForm.LocalIntertwining` unramified set (WORKORDER LI-1).

  The set's headline is `NumberField.TateGlobal.WeylUnramified.integral_unramifiedWeylIntegrand_adicCompletion`.
  Each zone below is a real, executed composition over it: deleting `WeylShell.lean` (which the
  headline's proof consumes) or `WeylPrelude.lean` (the definition layer) makes this file fail to
  elaborate. The zones are hypothesis-form — the concrete instantiations (a number field, a place,
  a Haar measure) are not ported — and no `#check` stands in for a composition.

  Outside every library, deliberately: `spec/` is not part of `FLTForHuman`, so neither this file
  nor its imports can slow or break the verified build. Run:
    `lake env lean -DautoImplicit=false -DmaxHeartbeats=4000000 spec/LocalIntertwiningConsumer.lean`
-/
import FLTForHuman.NumberTheory.NumberField.TateGlobal.WeylUnramified
import FLTForHuman.NumberTheory.NumberField.TateGlobal.WeylSmooth

open MeasureTheory NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Set
open scoped NNReal ENNReal Pointwise
open NumberField.TateGlobal WeylUnramified WeylPrelude WeylSmooth

noncomputable section

namespace FLTForHuman.Consumer.LocalIntertwining

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}
  [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
  {μ : Measure (v.adicCompletion F)} [μ.IsAddHaarMeasure]

/-- **Zone A — the unramified headline at the trivial character.** The headline is stated for an
unramified character `χ` of the unit group; at `χ = 1` the two character factors collapse to `1`
and the hypothesis `hχ` is `map_one`, so the identity is a genuine corollary of the headline and
not a restatement. This is the composition the pin uses downstream (the Euler factor at an
unramified place). -/
theorem integral_unramifiedWeylIntegrand_adicCompletion_trivial
    (ϖ : (v.adicCompletion F)ˣ)
    (hϖ : Valued.v (ϖ : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (s : ℂ)
    (hs : ‖(1 : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s))‖ < 1) :
    ∫ x, ((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (fun _ => (1 : ℂ)) x
          + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
              (fun y => LanglandsTunnell.TateLocal.charExt (1 : (v.adicCompletion F)ˣ →* ℂˣ)⁻¹ y
                * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1))) x)
        ∂μ
      = (μ.real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) : ℂ)
          * (1 - (1 : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1)))
          * (1 - (1 : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s)))⁻¹ :=
  integral_unramifiedWeylIntegrand_adicCompletion F v μ ϖ hϖ
    (1 : (v.adicCompletion F)ˣ →* ℂˣ) (fun _ _ => rfl) s (by simpa using hs)

/-- **Zone B — the definition layer is reachable through the headline's module.** `normQ` and the
negShell measure API are the prelude the headline's proof consumes; naming them here proves the
module graph, not just the headline. -/
example {ϖ : v.adicCompletionIntegers F} (hπ : Irreducible ϖ) (m : ℕ) :
    MeasurableSet (negShell (v := v) hπ m) ∧ (1 : ℝ≥0) ≤ normQ v :=
  ⟨measurableSet_negShell (v := v) hπ m, one_le_normQ (v := v)⟩

/-- **Zone C — the smooth headline at `m = 1`.** The headline's middle term is a sum over
`Finset.Ico 1 m` and its last term carries `(·) ^ m`; at `m = 1` the sum is empty and the power is
the identity, which is the form the pin's own consumers use. Specialising the headline is a real
composition: deleting `WeylSmooth.lean` (or any module its private development imports) breaks it. -/
theorem integral_smoothWeylIntegrand_adicCompletion_one
    (ϖ : (v.adicCompletion F)ˣ)
    (hϖ : Valued.v (ϖ : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (χ : (v.adicCompletion F)ˣ →* ℂˣ)
    (hχ : ∃ c : ℕ, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt F v c, χ u = 1)
    (A : v.adicCompletion F → ℂ)
    (hA : IntegrableOn A (v.adicCompletionIntegers F : Set (v.adicCompletion F)) μ)
    (B : v.adicCompletion F → ℂ)
    (hB : ∀ x y : v.adicCompletion F,
      Valued.v (y - x) ≤ Multiplicative.ofAdd (-(1 : ℤ)) → B y = B x)
    (s : ℂ)
    (hs : ‖((χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s))‖ < 1) :
    ∫ x, ((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator A x
          + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
              (fun y => LanglandsTunnell.TateLocal.charExt χ⁻¹ y
                * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1)) * B y⁻¹) x)
        ∂μ
      = (∫ x in (v.adicCompletionIntegers F : Set (v.adicCompletion F)), A x ∂μ)
        + B 0 * (∫ u in {u : v.adicCompletion F | Valued.v u = 1},
              LanglandsTunnell.TateLocal.charExt χ⁻¹ u ∂μ)
            * (((χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s)))
            * (1 - ((χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s)))⁻¹ := by
  simpa using
    integral_smoothWeylIntegrand_adicCompletion F v μ ϖ hϖ χ hχ 1 le_rfl A hA B hB s hs

end FLTForHuman.Consumer.LocalIntertwining
