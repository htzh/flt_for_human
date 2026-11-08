/-
  Consumer zone for `FLTForHuman/AutomorphicForm/Adelic/WeylTranslateValues.lean` (order AF37B).

  A `spec/` probe, not a library module: it *consumes* the two headlines in composition, never by
  `#check`.

  The two headlines are the two Weyl-translate evaluations of one induced section `φ` of the
  character pair `(etaFst 1 α hα s, etaSnd 1 α hα s)`:

  * `apply_weylInv_unipotent_mul_archSupportedAt_eq_norm_cpow_mul_apply` — at one infinite place
    `w`, with `k` compact at the other infinite places and trivial at every finite place,
    `φ (w⁻¹ n(x) k) = ‖det k_w‖^(s+1/2) ‖k_w00 + x_w k_w10‖^(-(2s+1)) · φ (w⁻¹ n(x'))`;
  * `apply_weylInv_unipotent_mul_localWeyl_eq_modulus_cpow_mul_apply` — at one finite place `v`,
    `φ (w⁻¹ n(x) finEmbed (localEmbed v gl2Weyl)) = modulus (x_v)^(-(2s+1)) · φ (w⁻¹ n(x'))`.

  Both are instances of the induced law, and both scalars are *values of the character pair* on the
  Borel component of the same Bruhat factorisation; the zones below read off what that means on the
  overlap where the scalars are trivial, and then put the two evaluations side by side.

  * **Zone 1** evaluates the finite-place headline at a *unit* finite component `x_v = 1`: the
    modulus factor is `modulus 1 = 1` and drops out, so the finite Weyl translate of `φ` moves the
    point `x` to the corrected point and changes nothing else. This is the value-side content of
    the induced law at the identity of the finite place.

  * **Zone 2** evaluates the archimedean headline at the trivial compact `k = 1`: `k_w = 1`, so
    `det k_w = 1` and `k_w00 + x_w k_w10 = 1`, both `‖·‖`-powers collapse to `1`, and the correction
    `x'` of the statement is `x` itself. The archimedean evaluation is thus the identity on such
    sections — the other end of the same computation.

  * **Zone 3** composes them: at a unit finite component the finite-place translate of `φ` lands on
    the same value as the trivial archimedean translate of `φ` at the corrected point. The two
    headlines are about the same `φ`, the same `s` and the same character pair, so their
    instantiations compose without any further input.

  `spec/` is outside every Lake library, so this file is checked by
  `lake env lean spec/AutomorphicFormSetAF37BConsumer.lean` and never enters the build.
-/
import FLTForHuman.AutomorphicForm.Adelic.WeylTranslateValues
import FLTForHuman.NumberTheory.NumberField.TateGlobal.NormIntegrable

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain
open AutomorphicForm AdelicDock
open scoped NNReal Classical

namespace AutomorphicFormSetAF37BConsumer

variable {F : Type} [Field F] [NumberField F]

/-- The modulus character of both headlines, as they spell it. -/
abbrev alphaOf : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
  ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
    (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits

/-- The corrected finite point of the local headline. -/
abbrev splOf (v : HeightOneSpectrum (𝓞 F)) (x : AdeleRing (𝓞 F) F) : AdeleRing (𝓞 F) F :=
  (x.1, AdelicDock.splice (𝓞 F) F v x.2 (x.2 v)⁻¹)

/-- **Zone 1.** The finite-place evaluation at a unit finite component: the modulus factor is
`modulus 1 = 1`, so the finite Weyl translate carries the value of `φ` over to the corrected
point and multiplies by nothing. -/
theorem localWeyl_unit_value
    (hα : ∀ t, 0 < ((alphaOf (F := F) t : ℝˣ) : ℝ)) (s : ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : IsInducedSection (𝓞 F) F (etaFst 1 (alphaOf (F := F)) hα s)
      (etaSnd 1 (alphaOf (F := F)) hα s) φ)
    (v : HeightOneSpectrum (𝓞 F)) (x : AdeleRing (𝓞 F) F) (hx : x.2 v = 1) :
    φ ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x
          * AdelicDock.finEmbed (𝓞 F) F (AdelicDock.localEmbed (𝓞 F) F v gl2Weyl))
      = φ ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 (splOf v x)) := by
  have hx0 : x.2 v ≠ 0 := by rw [hx]; exact one_ne_zero
  have h := apply_weylInv_unipotent_mul_localWeyl_eq_modulus_cpow_mul_apply
    F hα s φ hφ v x hx0
  rw [h]
  have hm : LanglandsTunnell.TateLocal.modulus (x.2 v) = 1 := by
    rw [hx, NumberField.TateGlobal.modulus_adicCompletion_eq_nnnorm]
    simp
  rw [hm]
  norm_num

/-- **Zone 2.** The archimedean evaluation at the trivial compact `k = 1`: `k_w = 1`, so both
`‖·‖`-powers are `1` and the correction point of the statement is `x` itself. -/
theorem archSupportedAt_one
    (hα : ∀ t, 0 < ((alphaOf (F := F) t : ℝˣ) : ℝ)) (s : ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : IsInducedSection (𝓞 F) F (etaFst 1 (alphaOf (F := F)) hα s)
      (etaSnd 1 (alphaOf (F := F)) hα s) φ)
    (w : InfinitePlace F) (x : AdeleRing (𝓞 F) F) :
    φ ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x * (1 : AdelicGL2 (𝓞 F) F))
      = φ ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x) := by
  have hka : ∀ w' : InfinitePlace F, w' ≠ w →
      archComponent F w' (glArch (𝓞 F) F (1 : AdelicGL2 (𝓞 F) F)) = 1 := by
    intro w' _; simp
  have hmat : ((archComponent F w (glArch (𝓞 F) F (1 : AdelicGL2 (𝓞 F) F)) :
      GL (Fin 2) w.Completion)) = 1 := by simp
  have h := apply_weylInv_unipotent_mul_archSupportedAt_eq_norm_cpow_mul_apply
    F hα s φ hφ w (1 : AdelicGL2 (𝓞 F) F) (by simp) hka x (by rw [hmat]; simp)
  rw [h]
  have hx' : (Function.update x.1 w (x.1 w), x.2) = x := by
    rw [show Function.update x.1 w (x.1 w) = x.1 from Function.update_eq_self w x.1]
    exact Prod.ext rfl rfl
  simp
  exact congrArg (fun y => φ ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 y)) hx'

/-- **Zone 3.** The two evaluations composed: at a unit finite component, the finite-place Weyl
translate of `φ` and the trivial archimedean translate of `φ` at the corrected point agree. -/
theorem localWeyl_eq_archSupportedAt
    (hα : ∀ t, 0 < ((alphaOf (F := F) t : ℝˣ) : ℝ)) (s : ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : IsInducedSection (𝓞 F) F (etaFst 1 (alphaOf (F := F)) hα s)
      (etaSnd 1 (alphaOf (F := F)) hα s) φ)
    (w : InfinitePlace F) (v : HeightOneSpectrum (𝓞 F)) (x : AdeleRing (𝓞 F) F)
    (hx : x.2 v = 1) :
    φ ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x
          * AdelicDock.finEmbed (𝓞 F) F (AdelicDock.localEmbed (𝓞 F) F v gl2Weyl))
      = φ ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 (splOf v x) * (1 : AdelicGL2 (𝓞 F) F)) := by
  rw [localWeyl_unit_value hα s φ hφ v x hx, archSupportedAt_one hα s φ hφ w (splOf v x)]

end AutomorphicFormSetAF37BConsumer
