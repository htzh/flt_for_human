/-
  SET-AF88A consumer: a depth for a single level-invariant function, and the reflexion convolution.

  **The rows.** `FLTForHuman/AutomorphicForm/Adelic/RightTranslateSpan.lean` carries the tensor split of a
  finitely-generated right-translate span, the *depth* a finite sum of right translates acquires, and the
  preservation of archimedean bi-finiteness under the reflexion convolution.

  **The readings.** Zone 1 is the depth row at `r = 1`: a single level-invariant function — not a sum — has a
  depth `n` such that `lowerUnipotentGL2 γ` acts trivially for every `γ` that is integral outside `S` and
  deep enough inside it. Zone 2 unpacks the reflexion row at concrete type families: the convolution of `f'`
  with `x ↦ f x⁻¹` is archimedean-bi-finite for *some* family, which is the form a downstream statement cites.

  `spec/` is outside every Lake library, so this file is checked by
  `lake env lean spec/AutomorphicFormSetAF88AConsumer.lean` and never enters the build.
-/
import FLTForHuman.AutomorphicForm.Adelic.RightTranslateSpan

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel IsDedekindDomain
open AutomorphicForm
open scoped Classical ENNReal NNReal Matrix BigOperators ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

namespace AutomorphicFormSetAF88AConsumer

/-- **Zone 1.** A single level-invariant function has a depth: `r = 1` in the depth row. -/
theorem exists_depth_of_levelInvariant
    (K : Type) [Field K] [NumberField K]
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (x₀ : AdelicGL2 (𝓞 K) K → ℂ)
    (hx₀lev : ∀ g : AdelicGL2 (𝓞 K) K,
      ∀ k ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, x₀ (g * k) = x₀ g) :
    ∃ n : ℕ, 0 < n ∧ ∀ (γ : AdeleRing (𝓞 K) K) (g : AdelicGL2 (𝓞 K) K), γ.1 = 0 →
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → γ.2 v = 0) →
      (∀ v ∈ S, Valued.v (γ.2 v) ≤
        ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) →
      x₀ (g * lowerUnipotentGL2 γ) = x₀ g := by
  obtain ⟨n, hn, h⟩ := exists_depth_forall_apply_mul_lowerUnipotentGL2_eq_of_sum_translate
    K N hN S x₀ hx₀lev 1 (fun _ => 1) (fun _ => 1) x₀ (by intro g; simp)
  refine ⟨n, hn, fun γ g hγ0 hout hS => ?_⟩
  simpa using h γ g hγ0 hout hS

/-- **Zone 2.** The reflexion convolution of two archimedean-bi-finite, continuous, compactly supported
functions is archimedean-bi-finite for some type family. -/
theorem exists_archBiFinite_rightConv_comp_inv (F : Type) [Field F] [NumberField F]
    (f f' : AdelicGL2 (𝓞 F) F → ℂ) (tys tys' : ArchTypeFamily F)
    (hfc : Continuous f) (hfs : HasCompactSupport f) (hbf : IsArchBiFinite F tys f)
    (hfc' : Continuous f') (hfs' : HasCompactSupport f') (hbf' : IsArchBiFinite F tys' f') :
    ∃ tys'' : ArchTypeFamily F, IsArchBiFinite F tys'' (rightConv F f' (fun x => f x⁻¹)) :=
  exists_isArchBiFinite_rightConv_comp_inv F f f' tys tys' hfc hfs hbf hfc' hfs' hbf'

end AutomorphicFormSetAF88AConsumer
