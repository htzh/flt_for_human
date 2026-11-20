/-
  SET-AF89A consumer: the annihilator of the diagonal is exactly the diagonal.

  **The row.** `FLTForHuman/NumberTheory/AdelicFourier/Faithful.lean` carries
  `mem_range_algebraMap_of_forall_apply_mul_eq_one`: for a global additive character `ψ` of `𝔸_F`,
  `ψ (y * ξ) = 1` for every principal `ξ` forces `y` itself to be principal.

  **The reading.** The row is one half of the characterisation of the annihilator of the diagonal;
  the other half is the definition of *global* (`IsGlobalAddChar.principalInvariant`). Together they
  say `{y | ∀ ξ, ψ (y * ξ) = 1} = range (algebraMap F 𝔸)` — the self-duality statement the adelic
  Fourier transform uses, and the exact form in which the pin's proof consumes the row. The
  composition is the row plus the structure field, and it is the `Iff` a consumer wants; the row
  alone is only the hard direction.

  `spec/` is outside every Lake library, so this file is checked by
  `lake env lean spec/NumberFieldSetAF89AConsumer.lean` and never enters the build.
-/
import FLTForHuman.NumberTheory.AdelicFourier.Faithful

set_option autoImplicit false

noncomputable section

open IsDedekindDomain NumberField AutomorphicForm

namespace NumberField.AdelicFourier

/-- **The reading.** The annihilator of the diagonal in `𝔸_F` is the diagonal, for a global
additive character: the hard direction is the faithfulness row, the easy one is principal
invariance. -/
theorem forall_mul_eq_one_iff_mem_range
    (F : Type) [Field F] [NumberField F]
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ) (y : AdeleRing (𝓞 F) F) :
    (∀ ξ : F, ψ (y * algebraMap F (AdeleRing (𝓞 F) F) ξ) = 1) ↔
      y ∈ Set.range (algebraMap F (AdeleRing (𝓞 F) F)) := by
  refine ⟨mem_range_algebraMap_of_forall_apply_mul_eq_one F hψ y, ?_⟩
  rintro ⟨x, rfl⟩ ξ
  rw [← map_mul (algebraMap F (AdeleRing (𝓞 F) F)) x ξ, hψ.principalInvariant]

end NumberField.AdelicFourier
