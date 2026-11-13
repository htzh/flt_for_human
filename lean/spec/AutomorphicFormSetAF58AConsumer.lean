/-
  SET-AF58A consumer: the cuspidality bound, spent.

  **The row.** `FLTForHuman/AutomorphicForm/Adelic/CuspidalityBound.lean` (row A):
  `AutomorphicForm.norm_integral_mul_le_mul_setIntegral_norm_of_isCuspidalFn`, the bound

    `‖∫ y, φ y * f (x⁻¹ y)‖ ≤ ε * ∫ y in image2 (n t * x * c) (closure box) (tsupport f), ‖φ y‖`

  under the pointwise hypothesis that the unipotent average of `f` differs from the `adelicBox`
  normalised integral of `f` by at most `ε` everywhere.

  **The readings.** The row is an inequality in `ε`, so the consumer *spends* it twice, at the two
  ends where the inequality stops being an estimate:

  * Zone A1 (`ε = 0`): the average hypothesis at `ε = 0` says the unipotent `tsum` of `f` *is* the
    box average of `f` at every point.  The bound then reads `‖∫ φ y * f (x⁻¹ y)‖ ≤ 0`, i.e. the
    matrix coefficient integral vanishes.  This is the shape the arithmetic layer wants: a
    cuspidal `φ` pairs to zero against a test function whose unipotent average is exact.
  * Zone A2 (zero mass): the right-hand side is proportional to the mass of `φ` over the compact
    translate set `image2 (n t * x * c) (closure box) (tsupport f)`.  When that mass vanishes the
    bound holds for *every* `ε`, so the integral vanishes — the row is what converts a vanishing
    `L¹` mass of `φ` on the support of the unfold into vanishing of the pairing.

  The statement-level data (`φ`, `f`, `x`, `hφN`, `hφi`, `hφc`, `hf`, `hfs`) cannot be instantiated
  concretely: they are properties of an arbitrary cuspidal form and an arbitrary compactly supported
  test function, so they enter in hypothesis form, which is the legitimate reading for this row.  The
  hypothesis `hP` — the unipotent-average defect bound — is exactly what the module's own
  `exists_weight` construction consumes, and it is the only data the row does not itself hand over.

  This module is outside every library: it is a spec-side composition check, not part of the port's
  import graph.
-/
import FLTForHuman.AutomorphicForm.Adelic.CuspidalityBound

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox
open IsDedekindDomain AutomorphicForm
open scoped ENNReal Topology ProbabilityTheory

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

namespace AutomorphicForm.SetAF58AConsumer

variable (K : Type) [Field K] [NumberField K]

/-- **Zone A1, the bound at `ε = 0`.**  If the unipotent average of `f` equals the `adelicBox`
normalised integral of `f` at every point, the cuspidality bound gives `‖∫ φ y * f (x⁻¹ y)‖ ≤ 0`,
so the pairing of a cuspidal `φ` against such an `f` vanishes. -/
theorem consumer_A_pairing_vanishes_at_zero
    (φ f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (x : GL (Fin 2) (AdeleRing (𝓞 K) K))
    (hφN : ∀ (β : K) (y : GL (Fin 2) (AdeleRing (𝓞 K) K)),
      φ (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) * y) = φ y)
    (hφi : LocallyIntegrable φ (adelicGLHaar (Fin 2) (𝓞 K) K))
    (hφc : IsCuspidalFn ((adelicAddHaar (𝓞 K) K)[|adelicBox K]) unipotentGL2 φ)
    (hf : Continuous f) (hfs : HasCompactSupport f)
    (hP : ∀ y, ‖(∑' β : K, f (x⁻¹ * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) * y))
        - (((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ)⁻¹ *
            ∫ t, f (x⁻¹ * unipotentGL2 t * y) ∂(adelicAddHaar (𝓞 K) K)‖ ≤ 0) :
    ∫ y, φ y * f (x⁻¹ * y) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0 := by
  have h := norm_integral_mul_le_mul_setIntegral_norm_of_isCuspidalFn K φ f x
    hφN hφi hφc hf hfs 0 hP
  rw [zero_mul] at h
  exact norm_eq_zero.mp (le_antisymm h (norm_nonneg _))

/-- **Zone A2, the bound against a vanishing mass.**  The right-hand side of the bound is `ε` times
the `L¹` mass of `‖φ‖` over the compact set `image2 (n t * x * c) (closure box) (tsupport f)`.  When
that mass is zero the inequality reads `‖∫ φ y * f (x⁻¹ y)‖ ≤ ε * 0` for every `ε ≥ 0`, so the
pairing vanishes outright: the row converts a vanishing mass of a cuspidal `φ` on the unfolded
support into a vanishing matrix coefficient. -/
theorem consumer_A_pairing_vanishes_of_zero_mass
    (φ f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (x : GL (Fin 2) (AdeleRing (𝓞 K) K))
    (hφN : ∀ (β : K) (y : GL (Fin 2) (AdeleRing (𝓞 K) K)),
      φ (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) * y) = φ y)
    (hφi : LocallyIntegrable φ (adelicGLHaar (Fin 2) (𝓞 K) K))
    (hφc : IsCuspidalFn ((adelicAddHaar (𝓞 K) K)[|adelicBox K]) unipotentGL2 φ)
    (hf : Continuous f) (hfs : HasCompactSupport f)
    (ε : ℝ)
    (hP : ∀ y, ‖(∑' β : K, f (x⁻¹ * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) * y))
        - (((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ)⁻¹ *
            ∫ t, f (x⁻¹ * unipotentGL2 t * y) ∂(adelicAddHaar (𝓞 K) K)‖ ≤ ε)
    (hmass : ∫ y in Set.image2 (fun (t : AdeleRing (𝓞 K) K)
          (c : GL (Fin 2) (AdeleRing (𝓞 K) K)) => unipotentGL2 t * x * c)
          (closure (adelicBox K)) (tsupport f),
          ‖φ y‖ ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0) :
    ∫ y, φ y * f (x⁻¹ * y) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0 := by
  have h := norm_integral_mul_le_mul_setIntegral_norm_of_isCuspidalFn K φ f x
    hφN hφi hφc hf hfs ε hP
  rw [hmass, mul_zero] at h
  exact norm_eq_zero.mp (le_antisymm h (norm_nonneg _))

end AutomorphicForm.SetAF58AConsumer
