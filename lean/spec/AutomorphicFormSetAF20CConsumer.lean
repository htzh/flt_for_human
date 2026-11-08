/-
  Cross-module wire test for SET-AF20C (the rational (centre-)unipotent Haar measures).

  A `spec/` probe, not a library module. **One zone**, and it composes both headlines of
  `AutomorphicForm/Adelic/RationalUnipotentHaar.lean`:

  * the **centre headline**
    (`isHaarMeasure_rationalCentreUnipotentHaar_and_isMulRightInvariant`) says that
    `rationalCentreUnipotentHaar K` is a Haar measure and right-invariant;
  * the **torus headline** (`isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant`)
    says the same for `rationalTorusUnipotentHaar K`.

  The zone reads, from each headline, one consequence of the two halves: the right-invariance is
  applied at a *concrete* element — the rational scalar times unipotent element
  `globalPoints (scalar a) * unipotentGL2 x` for the centre and
  `globalPoints (scalar za.1) * globalPoints (diagOne za.2) * unipotentGL2 x` for the torus — and
  the `IsHaarMeasure` half is read as finiteness on compact sets, which is where the discreteness
  of `K` in `𝔸_K` enters. It dies if either headline loses a statement: neither the
  right-invariance nor the finiteness of one measure follows from the other.

  It imports only the module it composes.
-/
import FLTForHuman.AutomorphicForm.Adelic.RationalUnipotentHaar

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox NumberField.AdelicLevel
open AutomorphicForm
open scoped ENNReal

noncomputable section

namespace SetAF20CUnipotentHaarConsumer

variable (K : Type) [Field K] [NumberField K]

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

/-- **Zone A — both headlines, at a concrete element, and finite on compacts.** The right-invariant
half of each headline is read at the rational (torus-)scalar times unipotent element built from
`globalPoints (scalar a) * unipotentGL2 x`; the Haar half is read as `μ C < ⊤` for every compact
`C`, which is `IsFiniteMeasureOnCompacts` — the discreteness input of the proof. -/
theorem headlines_composed (a : Kˣ) (x : AdeleRing (𝓞 K) K) (za : Kˣ × Kˣ) :
    let gC : rationalCentreUnipotent K :=
      ⟨globalPoints (𝓞 K) K
          (Units.map (Matrix.scalar (Fin 2) : K →+* Matrix (Fin 2) (Fin 2) K).toMonoidHom a) *
        unipotentGL2 x, Subgroup.mul_mem_sup ⟨a, rfl⟩ ⟨Multiplicative.ofAdd x, rfl⟩⟩
    let gT : rationalTorusUnipotent K :=
      ⟨globalPoints (𝓞 K) K
          (Units.map (Matrix.scalar (Fin 2) : K →+* Matrix (Fin 2) (Fin 2) K).toMonoidHom za.1) *
        globalPoints (𝓞 K) K (diagOne za.2) * unipotentGL2 x,
        Subgroup.mul_mem_sup
          (Subgroup.mul_mem_sup ⟨za.1, rfl⟩ ⟨za.2, rfl⟩) ⟨Multiplicative.ofAdd x, rfl⟩⟩
    (rationalCentreUnipotentHaar K).map (fun y => y * gC) = rationalCentreUnipotentHaar K ∧
      (rationalTorusUnipotentHaar K).map (fun y => y * gT) = rationalTorusUnipotentHaar K ∧
      (∀ C : Set (rationalCentreUnipotent K), IsCompact C →
        (rationalCentreUnipotentHaar K) C < ⊤) ∧
      (∀ C : Set (rationalTorusUnipotent K), IsCompact C →
        (rationalTorusUnipotentHaar K) C < ⊤) := by
  obtain ⟨hhaarC, hrightC⟩ :=
    isHaarMeasure_rationalCentreUnipotentHaar_and_isMulRightInvariant K
  obtain ⟨hhaarT, hrightT⟩ :=
    isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant K
  refine ⟨hrightC.map_mul_right_eq_self _, hrightT.map_mul_right_eq_self _, ?_, ?_⟩
  · intro C hC
    have := hhaarC.toIsFiniteMeasureOnCompacts
    exact hC.measure_lt_top
  · intro C hC
    have := hhaarT.toIsFiniteMeasureOnCompacts
    exact hC.measure_lt_top

end SetAF20CUnipotentHaarConsumer

end
