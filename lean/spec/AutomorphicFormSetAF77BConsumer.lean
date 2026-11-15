/-
  Consumer zone for `FLTForHuman/AutomorphicForm/Adelic/WeylIntegrable/PureTensorProd.lean`
  (`AF77B`).

  A `spec/` probe, not a library module. The zone is read at `F = ℚ`, `S = ∅` and `s = 1`: the
  finite product `∏ v ∈ S` is `1` on both sides, the fibre product `∏ᶠ v : {v // v ∉ S}` runs over
  the whole family, and the half-plane hypothesis `1 / 2 < s.re` is discharged by `norm_num`. The
  data are concrete: the constant function `fOne` on the mixed space, the constant local function
  `hOne`, the trivial local character `chiOne`, the additive Haar measure `adelicAddHaar` on the
  adèles of `ℚ`, and `Measure.addHaar` at every finite place.

  Every zone is a real composition — no `#check` — so deleting the module (or leaving a hole in it)
  breaks this file:

  * `weylFactor` is the row's local unramified Weyl integrand at `F = ℚ`: the
    `adicCompletionIntegers` indicator `1` plus the complement indicator carrying the Tate twist;
  * `weylFactor_of_mem_integers` is that integrand on the integral adèles, where the row's factor
    is the plain `1` — the indicator split collapsing;
  * `pureTensor_prod_mul_eulerProduct` is the headline itself at `S = ∅`, with the finite product
    read as `1` (`Finset.prod_empty`) and the two Euler products left at their own exponents
    `-(2 * s)` and `-(2 * s + 1)` — the row's `2s` versus `2s + 1` bookkeeping;
  * `pureTensor_at_one` is that identity at `s = 1`, where the half-plane hypothesis is discharged
    numerically and the exponents become `-2` and `-3`.

  `spec/` is outside every Lake library, so this file is checked by
  `lake env lean spec/AutomorphicFormSetAF77BConsumer.lean` and never enters the build.
-/
import FLTForHuman.AutomorphicForm.Adelic.WeylIntegrable.PureTensorProd

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.InfinitePlace NumberField.AdelicBox
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum AutomorphicForm.LocalIntertwining
open scoped ENNReal NNReal Classical Topology BigOperators

namespace AutomorphicFormSetAF77BConsumer

attribute [local instance] NumberField.AdelicHaar.adeleBorel
attribute [local instance] NumberField.AdelicHaar.borelSpace_adeleBorel
attribute [local instance] NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

/-! ### The concrete data at `F = ℚ` -/

/-- The pure tensor's archimedean factor: the constant `1` on the mixed space. -/
def fOne : mixedEmbedding.mixedSpace ℚ → ℂ := fun _ => 1

/-- The local factor at every finite place: the constant `1`. -/
def hOne (v : HeightOneSpectrum (𝓞 ℚ)) : v.adicCompletion ℚ → ℂ := fun _ => 1

/-- The local character at every finite place: the trivial one. -/
def chiOne (v : HeightOneSpectrum (𝓞 ℚ)) : (v.adicCompletion ℚ)ˣ →* ℂˣ := 1

/-- The row's local unramified Weyl integrand at `F = ℚ`: `1` on the adelic integers, the Tate twist
`charExt χ⁻¹ y * ‖y‖ ^ (-(2 * s + 1))` off them. -/
def weylFactor (χ : ∀ v : HeightOneSpectrum (𝓞 ℚ), (v.adicCompletion ℚ)ˣ →* ℂˣ) (s : ℂ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (y : v.adicCompletion ℚ) : ℂ :=
  (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)).indicator (fun _ => (1 : ℂ)) y
    + (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ))ᶜ.indicator
        (fun y => LanglandsTunnell.TateLocal.charExt (χ v)⁻¹ y
          * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1))) y

/-- On the integral adèles the row's factor is the plain `1`: the twisted indicator is off and the
constant one is on, so the indicator split collapses. -/
theorem weylFactor_of_mem_integers (χ : ∀ v : HeightOneSpectrum (𝓞 ℚ), (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (s : ℂ) (v : HeightOneSpectrum (𝓞 ℚ)) (y : v.adicCompletion ℚ)
    (hy : y ∈ (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ))) :
    weylFactor χ s v y = 1 := by
  rw [weylFactor, Set.indicator_of_mem hy, Set.indicator_of_notMem (by simpa using hy)]
  simp

/-! ### The headline at `F = ℚ`, `S = ∅` -/

/-- The row at `F = ℚ`, `S = ∅`, concrete `f`, `h`, `χ` and a general point of the half-plane: the
box-normalized `𝔸_ℚ`-integral of the pure tensor against the whole-family Weyl product, times the
Euler product at exponent `-(2 * s)`, equals the discriminant factor times the archimedean integral
times the Euler product at `-(2 * s + 1)`. Both finite products over `S = ∅` are `1`. -/
theorem pureTensor_prod_mul_eulerProduct
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 ℚ), (v.adicCompletion ℚ)ˣ)
    (hϖ : ∀ v ∉ (∅ : Finset (HeightOneSpectrum (𝓞 ℚ))),
      Valued.v (ϖ v : v.adicCompletion ℚ) = Multiplicative.ofAdd (-1 : ℤ))
    (s : ℂ) (hs : 1 / 2 < s.re) :
    ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ (adelicBox ℚ)).toReal : ℂ)⁻¹
        * (∫ x, fOne (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ x.1)
              * ∏ᶠ v : {v : HeightOneSpectrum (𝓞 ℚ) //
                    v ∉ (∅ : Finset (HeightOneSpectrum (𝓞 ℚ)))},
                  weylFactor chiOne s v.1 (x.2 v.1)
              ∂NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)
        * ∏' v : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ (∅ : Finset (HeightOneSpectrum (𝓞 ℚ)))},
            (1 - ((chiOne v.1 (ϖ v.1) : ℂˣ) : ℂ)
              * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s)))
      = (((2 : ℝ) ^ nrComplexPlaces ℚ / Real.sqrt |(discr ℚ : ℝ)| : ℝ) : ℂ)
        * (∫ y, fOne y)
        * ∏' v : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ (∅ : Finset (HeightOneSpectrum (𝓞 ℚ)))},
            (1 - ((chiOne v.1 (ϖ v.1) : ℂˣ) : ℂ)
              * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1))) := by
  let : ∀ v : HeightOneSpectrum (𝓞 ℚ), MeasurableSpace (v.adicCompletion ℚ) := fun v => borel _
  have : ∀ v : HeightOneSpectrum (𝓞 ℚ), BorelSpace (v.adicCompletion ℚ) := fun v => ⟨rfl⟩
  have : ∀ v : HeightOneSpectrum (𝓞 ℚ),
      (Measure.addHaar : Measure (v.adicCompletion ℚ)).IsAddHaarMeasure := fun v => inferInstance
  have hrow :=
    integral_adeleRing_pureTensor_prod_mul_finprod_unramifiedWeylIntegrand_mul_tprod
      ℚ (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)
      (∅ : Finset (HeightOneSpectrum (𝓞 ℚ)))
      (fun v => (Measure.addHaar : Measure (v.adicCompletion ℚ))) fOne hOne ϖ hϖ chiOne
      (fun v _ u _ => rfl) (fun v _ => by simp [chiOne]) s hs
  simpa only [Finset.prod_empty, one_mul, weylFactor] using hrow

/-- The same row at `s = 1`: the half-plane hypothesis is `norm_num`, and the two Euler products
stand at `-2` and `-3`. -/
theorem pureTensor_at_one
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 ℚ), (v.adicCompletion ℚ)ˣ)
    (hϖ : ∀ v ∉ (∅ : Finset (HeightOneSpectrum (𝓞 ℚ))),
      Valued.v (ϖ v : v.adicCompletion ℚ) = Multiplicative.ofAdd (-1 : ℤ)) :
    ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ (adelicBox ℚ)).toReal : ℂ)⁻¹
        * (∫ x, fOne (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ x.1)
              * ∏ᶠ v : {v : HeightOneSpectrum (𝓞 ℚ) //
                    v ∉ (∅ : Finset (HeightOneSpectrum (𝓞 ℚ)))},
                  weylFactor chiOne 1 v.1 (x.2 v.1)
              ∂NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)
        * ∏' v : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ (∅ : Finset (HeightOneSpectrum (𝓞 ℚ)))},
            (1 - ((chiOne v.1 (ϖ v.1) : ℂˣ) : ℂ)
              * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * (1 : ℂ))))
      = (((2 : ℝ) ^ nrComplexPlaces ℚ / Real.sqrt |(discr ℚ : ℝ)| : ℝ) : ℂ)
        * (∫ y, fOne y)
        * ∏' v : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ (∅ : Finset (HeightOneSpectrum (𝓞 ℚ)))},
            (1 - ((chiOne v.1 (ϖ v.1) : ℂˣ) : ℂ)
              * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * (1 : ℂ) + 1))) :=
  pureTensor_prod_mul_eulerProduct ϖ hϖ 1 (by norm_num)

end AutomorphicFormSetAF77BConsumer

end
