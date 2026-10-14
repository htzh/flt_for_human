/-
  The tier-1 façade for WORKORDER-KF1
  (`topics/automorphicForm/WORKORDER-KF1-kfinite-family-span.md`): the Deligne–Serre
  leaf `AutomorphicForm.exists_isOpen_forall_exists_apply_eq_sum_of_isArchKFinite_of_continuous`.

  The headline is stated verbatim from the pin `Theorems/` wrapper (pinned `aa2d8b3`) and
  delegates to the tier-3 engine kernel
  `AutomorphicForm.ArchKFiniteFamily.Engine.exists_isOpen_forall_exists_apply_eq_sum_of_isArchKFinite_of_continuous`
  in `FLTForHuman/AutomorphicForm/Adelic/ArchKFiniteFamily.lean`, whose generic half is
  `FLTForHuman/RepTheory/TranslateSpan.lean`. Both engines stay tier 3 and unlisted.
-/
import FLTForHuman.AutomorphicForm.Adelic.ArchKFiniteFamily

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel
open AutomorphicForm AutomorphicForm.WindowedSiegel

-- pin: exists_isOpen_forall_exists_apply_eq_sum_of_isArchKFinite_of_continuous (Theorems/Thm_AutomorphicForm_exists_isOpen_forall_exists_apply_eq_sum_of_isArchKFinite_of_continuous.lean:10)
theorem AutomorphicForm.exists_isOpen_forall_exists_apply_eq_sum_of_isArchKFinite_of_continuous
    (F : Type) [Field F] [NumberField F]
    (φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
    (_hφK : ∀ s, IsArchKFinite F (φ s))
    (_hφf : ∀ s, IsKfSmooth F (φ s))
    (_hφjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φ p.1 p.2)) :
    ∃ U : Set ℂ, IsOpen U ∧ U.Nonempty ∧
      ∃ (n : ℕ) (σ : Fin n → ℂ), ∀ s ∈ U, ∃ c : Fin n → ℂ, ∀ k : AdelicGL2 (𝓞 F) F,
        glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F →
        (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) →
        φ s k = ∑ i, c i * φ (σ i) k :=
  AutomorphicForm.ArchKFiniteFamily.Engine.exists_isOpen_forall_exists_apply_eq_sum_of_isArchKFinite_of_continuous
    F φ _hφK _hφf _hφjc
