/-
  SET-AF57A consumer: the constant term's unipotent invariance, spent; the cuspidal unfolding,
  read off at its integral shape.

  **The zone.** Two rows in two modules, hence two executed compositions:

  * `FLTForHuman/AutomorphicForm/Adelic/ConstantTermUnipotent.lean` (V):
    `AutomorphicForm.constantTerm_adelicBox_unipotentGL2_mul`;
  * `FLTForHuman/AutomorphicForm/Adelic/CuspidalUnfolding.lean` (U):
    `AutomorphicForm.integral_mul_eq_integral_mul_weight_mul_tsum_sub_average_of_isCuspidalFn`.

  **The readings.**

  * Zone V. The row is the invariance of the `adelicBox`-conditioned constant term along the
    rational unipotent flow: `ct (n x₀ * g) = ct g` for every `x₀` and every `φ` invariant under the
    rational points `n (K)`.  The consumer *spends* it as an invariance and not as a formula: the
    vanishing of the constant term — cuspidality — is carried from `g` to the translated point
    `n x₀ * g`, i.e. the whole zero set of `ct` is stable under the flow.  That is what the
    cuspidal layer needs: a cuspidal `φ` stays cuspidal along `n (𝔸)`, so the vanishing may be
    checked at any point of the orbit of `g` under `n (x₀)`.
  * Zone U. The row is the unfolding identity
    `∫ φ y * f (x⁻¹ y) = ∫ φ y * w y * (∑' β, f (x⁻¹ n(β) y) - (μ box)⁻¹ * ∫ t, f (x⁻¹ n(t) y))`.
    The consumer *reads it off at its `tsum`/integral shape*: the weighted unipotent `tsum`
    integral splits off the weighted box average, so that when the weighted average contributes
    nothing (`havg`), the plain integral is the weighted unipotent `tsum` integral.  The
    integrability of the two split halves is stated in hypothesis form: it is exactly what the
    module's own `integrable_and_integral_mul_weight_mul_average_eq_zero` supplies, and it is the
    only data the row does not itself hand over.

  Statement-level data (`φ`, `f`, `x`, `w`, `hφN`, `hφi`, `hφc`, `hw`, `hw0`, `hw1`) cannot be
  instantiated concretely — they are properties of an arbitrary cuspidal form, an arbitrary
  compactly supported test function and an arbitrary partition weight — so they enter in hypothesis
  form, which is the legitimate reading for these rows.

  This module is outside every library: it is a spec-side composition check, not part of the
  port's import graph.
-/
import FLTForHuman.AutomorphicForm.Adelic.ConstantTermUnipotent
import FLTForHuman.AutomorphicForm.Adelic.CuspidalUnfolding

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox
open IsDedekindDomain AutomorphicForm
open scoped ENNReal Topology ProbabilityTheory

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

namespace AutomorphicForm.SetAF57AConsumer

/-! ### Zone V: the unipotent invariance, spent on cuspidality -/

section unipotentInvariance

variable (F : Type) [Field F] [NumberField F]

/-- **Zone V.** The zero set of the constant term is stable under the rational unipotent flow:
`φ` invariant under the rational points `n (K)` has vanishing constant term at `n x₀ * y` as soon
as it has vanishing constant term at `y`.  The invariance is used, not restated: the row rewrites
the constant term at the translated point into the one at `y`, and cuspidality finishes. -/
theorem consumer_V_cuspidal_along_unipotent
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : ∀ (k : F) (h : AdelicGL2 (𝓞 F) F),
      φ (globalPoints (𝓞 F) F (unipotentGL2 k) * h) = φ h)
    (x₀ : AdeleRing (𝓞 F) F)
    (hcuspidal : ∀ y : AdelicGL2 (𝓞 F) F,
      constantTerm ((adelicAddHaar (𝓞 F) F)[|adelicBox F]) (fun x => unipotentGL2 x) φ y = 0) :
    ∀ y : AdelicGL2 (𝓞 F) F,
      constantTerm ((adelicAddHaar (𝓞 F) F)[|adelicBox F]) (fun x => unipotentGL2 x) φ
        (unipotentGL2 x₀ * y) = 0 := by
  intro y
  rw [constantTerm_adelicBox_unipotentGL2_mul F hφ x₀ y, hcuspidal y]

end unipotentInvariance

/-! ### Zone U: the unfolding identity, read off at its `tsum`/integral shape -/

section unfolding

variable (K : Type) [Field K] [NumberField K]

/-- **Zone U.** The unfolding identity read off at its shape: the plain integral of `φ` against
`f (x⁻¹ ·)` is the weighted unipotent `tsum` integral once the weighted box-average half of the
unfolded integrand contributes nothing.  The row supplies the identity with the average subtracted
inside the integral; the consumer splits the difference with `integral_sub` (integrability of the
two halves is hypothesis-form data) and kills the average half with `havg`. -/
theorem consumer_U_unfolded_tsum_shape
    (φ f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (x : GL (Fin 2) (AdeleRing (𝓞 K) K))
    (hφN : ∀ (β : K) (y : GL (Fin 2) (AdeleRing (𝓞 K) K)),
      φ (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) * y) = φ y)
    (hφi : LocallyIntegrable φ (adelicGLHaar (Fin 2) (𝓞 K) K))
    (hφc : IsCuspidalFn ((adelicAddHaar (𝓞 K) K)[|adelicBox K]) unipotentGL2 φ)
    (hf : Continuous f) (hfs : HasCompactSupport f)
    (w : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℝ) (hw : Measurable w) (hw0 : ∀ y, 0 ≤ w y)
    (hw1 : ∀ (t : AdeleRing (𝓞 K) K) (c : GL (Fin 2) (AdeleRing (𝓞 K) K)), c ∈ tsupport f →
      ∑' β : K, w (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) *
        (unipotentGL2 t * x * c)) = 1)
    (hI₁ : Integrable (fun y => φ y * (w y : ℂ) *
        (∑' β : K, f (x⁻¹ * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) * y)))
        (adelicGLHaar (Fin 2) (𝓞 K) K))
    (hI₂ : Integrable (fun y => φ y * (w y : ℂ) *
        ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ)⁻¹ *
          ∫ t, f (x⁻¹ * unipotentGL2 t * y) ∂(adelicAddHaar (𝓞 K) K)))
        (adelicGLHaar (Fin 2) (𝓞 K) K))
    (havg : ∫ y, φ y * (w y : ℂ) *
        ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ)⁻¹ *
          ∫ t, f (x⁻¹ * unipotentGL2 t * y) ∂(adelicAddHaar (𝓞 K) K))
        ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0) :
    ∫ y, φ y * f (x⁻¹ * y) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)
      = ∫ y, φ y * (w y : ℂ) *
          (∑' β : K, f (x⁻¹ * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) * y))
          ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
  rw [AutomorphicForm.integral_mul_eq_integral_mul_weight_mul_tsum_sub_average_of_isCuspidalFn
    K φ f x hφN hφi hφc hf hfs w hw hw0 hw1]
  have hsplit : ∫ y, φ y * (w y : ℂ) *
        ((∑' β : K, f (x⁻¹ * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) * y))
          - (((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ)⁻¹ *
          ∫ t, f (x⁻¹ * unipotentGL2 t * y) ∂(adelicAddHaar (𝓞 K) K))
        ∂(adelicGLHaar (Fin 2) (𝓞 K) K)
      = ∫ y, φ y * (w y : ℂ) *
          (∑' β : K, f (x⁻¹ * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) * y))
          ∂(adelicGLHaar (Fin 2) (𝓞 K) K)
        - ∫ y, φ y * (w y : ℂ) *
            ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ)⁻¹ *
              ∫ t, f (x⁻¹ * unipotentGL2 t * y) ∂(adelicAddHaar (𝓞 K) K))
            ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
    rw [← integral_sub hI₁ hI₂]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    ring
  rw [hsplit, havg, sub_zero]

end unfolding

end AutomorphicForm.SetAF57AConsumer
