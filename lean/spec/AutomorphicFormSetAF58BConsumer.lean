/-
  SET-AF58B consumer: the fundamental domain and the Petersson self-pairing, spent.

  **The rows.** `FLTForHuman/AutomorphicForm/Adelic/GlobalPointsDomain.lean` (row C):
  `AutomorphicForm.exists_isFundamentalDomain_globalPoints_range`, the existence of a fundamental
  domain `D` for the global points `GL₂(K)` acting on `GL₂(𝔸_K)`; and
  `FLTForHuman/AutomorphicForm/Adelic/PeterssonSelfPairing.lean` (row B):
  `AutomorphicForm.peterssonIntegral_self_ne_zero_of_isFundamentalDomain_of_continuous`, the
  non-vanishing of the Petersson self-pairing of a continuous automorphic `x` on a fundamental
  domain inside a determinant slab.

  **The readings.**

  * Zone C1: the domain `D` is handed to the measure computation it exists for.  Since
    `GL₂(𝔸_K)` carries a Haar measure invariant under the global points, the measure of *any* set
    `T` decomposes as the sum over the countable group of the measures of its translates cut down
    to `D`, `μ T = ∑' γ, μ (γ • T ∩ D)`.  This is `IsFundamentalDomain.measure_eq_tsum` applied to
    the `D` that C produces: nothing about `D` is known besides C's statement, and the
    decomposition is exactly the reading of a fundamental domain as a measure-theoretic section.
  * Zone B1: the self-pairing is positive.  The pairing is the complexification of the real
    integral `∫ w in 𝓕, ‖x w‖ ^ 2 * ‖det w‖ ^ (-s)`, so B's headline gives
    `peterssonIntegral K w 𝓕 x x ≠ 0` and the toolkit's `setIntegral_norm_sq_wt_pos` gives
    positivity of that real integral; together, `0 < (peterssonIntegral K w 𝓕 x x).re`.

  The statement-level data of row B (`e₁`, `e₂`, `𝓕`, `h𝓕m`, `h𝓕s`, `h𝓕`, `x`, `hxc`, `hxG`,
  `hne`, `hint`) cannot be instantiated concretely: `𝓕` is an arbitrary measurable fundamental
  domain inside the slab and `x` an arbitrary continuous automorphic function, so they enter in
  hypothesis form, which is the legitimate reading for this row.

  This module is outside every library: it is a spec-side composition check, not part of the port's
  import graph.
-/
import FLTForHuman.AutomorphicForm.Adelic.GlobalPointsDomain
import FLTForHuman.AutomorphicForm.Adelic.PeterssonSelfPairing

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox
open IsDedekindDomain AutomorphicForm
open NumberField.TateGlobal
open scoped ENNReal Topology ProbabilityTheory Pointwise

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
attribute [local instance] NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar

namespace AutomorphicForm.SetAF58BConsumer

open PeterssonSelfPairing

/-- **Zone C1, the domain spent on a measure decomposition.**  The fundamental domain `D` that
row C produces makes the Haar measure of any set `T` the sum, over the global points, of the
measures of the translates of `T` cut down to `D`. -/
theorem consumer_C_measure_eq_tsum_of_fundamentalDomain (F : Type) [Field F] [NumberField F]
    (T : Set (AdelicGL2 (𝓞 F) F)) :
    ∃ D : Set (AdelicGL2 (𝓞 F) F),
      IsFundamentalDomain (globalPoints (𝓞 F) F).range D (adelicGLHaar (Fin 2) (𝓞 F) F) ∧
      (adelicGLHaar (Fin 2) (𝓞 F) F) T
        = ∑' γ : ↥(globalPoints (𝓞 F) F).range,
            (adelicGLHaar (Fin 2) (𝓞 F) F) (γ • T ∩ D) := by
  obtain ⟨D, hD⟩ := exists_isFundamentalDomain_globalPoints_range F
  exact ⟨D, hD, hD.measure_eq_tsum T⟩

/-- **Zone B1, the self-pairing is positive.**  On a measurable fundamental domain `𝓕` inside the
determinant slab `e₁ ≤ ‖det‖ ≤ e₂`, a continuous automorphic `x` that is non-zero somewhere in the
open slab has non-vanishing Petersson self-pairing, and that pairing is the complexification of a
strictly positive real integral. -/
theorem consumer_B_self_pairing_pos
    (K : Type) [Field K] [NumberField K]
    (w e₁ e₂ : ℝ) (he₁ : 0 < e₁) (he : e₁ < e₂)
    (𝓕 : Set (AdelicGL2 (𝓞 K) K)) (h𝓕m : MeasurableSet 𝓕)
    (h𝓕s : 𝓕 ⊆ {g | ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂})
    (h𝓕 : IsFundamentalDomain (globalPoints (𝓞 K) K).range 𝓕
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂}))
    (x : AdelicGL2 (𝓞 K) K → ℂ) (hxc : Continuous x)
    (hxG : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) K) (g : AdelicGL2 (𝓞 K) K),
      x (globalPoints (𝓞 K) K γ * g) = x g)
    (hne : ∃ g : AdelicGL2 (𝓞 K) K,
      ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Ioo e₁ e₂ ∧ x g ≠ 0)
    (hint : IntegrableOn (fun g => ‖x g‖ ^ 2 * ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (-w)) 𝓕
      (adelicGLHaar (Fin 2) (𝓞 K) K)) :
    peterssonIntegral K w 𝓕 x x ≠ 0 ∧ 0 < (peterssonIntegral K w 𝓕 x x).re := by
  have hz := peterssonIntegral_self_ne_zero_of_isFundamentalDomain_of_continuous K w e₁ e₂ he₁ he
    𝓕 h𝓕m h𝓕s h𝓕 x hxc hxG hne hint
  have hpos := PeterssonSelfPairing.setIntegral_norm_sq_wt_pos (F := K) h𝓕 w hxc hxG hne hint
  refine ⟨hz, ?_⟩
  rw [PeterssonSelfPairing.peterssonIntegral_self, Complex.ofReal_re]
  exact hpos

end AutomorphicForm.SetAF58BConsumer
