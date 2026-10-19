/-
  Whittaker coefficients of an adelic `GL₂`-function.

  `IsPrincipalInvariantAddChar ψ` says a character of the adele ring is trivial on the
  principal ideles; `IsGlobalAddChar ψ` bundles that with continuity and nontriviality (the
  standard global additive character of a number field is the unique-up-to-scalars instance).
  For carrier data `pins : CarrierPins F`, an additive character `ψ` and `φ` on
  `GL₂(𝔸_F)`,

    `whittakerCoefficient pins ψ φ α g = ∫ x, φ (unipotentGL2 x * g) * ψ (-(α * x)) ∂pins.ν`

  is the adelic Whittaker coefficient at the additive parameter `α : F`, integrated against
  the carrier's unipotent measure `pins.ν`; `WhittakerCoefficientIntegrable` is its
  integrability. The two lemmas record the degenerate cases: the coefficient of `0` vanishes,
  and at `α = 0` it is the constant term (`constantTerm` of `ConstantTerm.lean`).

  Transcribed verbatim from `Definitions/Def_AutomorphicForm_WhittakerCoefficient.lean`
  (pinned `aa2d8b3`, 61 lines, 8 declarations, no `private`; 653 pin importers). Its two
  `Definitions/` imports are the already-ported `CarrierPins` and `ConstantTerm`; the pin
  reached `AddChar` through `ConstantTerm`'s `import Mathlib`, so the one mathlib module that
  defines it is imported here explicitly.
-/
import FLTForHuman.AutomorphicForm.Adelic.CarrierPins
import FLTForHuman.AutomorphicForm.Adelic.ConstantTerm
import Mathlib.Algebra.Group.AddChar

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory
open AutomorphicForm

noncomputable section

namespace AutomorphicForm

variable (F : Type) [Field F] [NumberField F]

def IsPrincipalInvariantAddChar (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) : Prop :=
  ∀ α : F, ψ (algebraMap F (AdeleRing (𝓞 F) F) α) = 1

structure IsGlobalAddChar (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) : Prop where
  principalInvariant : IsPrincipalInvariantAddChar F ψ
  continuous : Continuous ψ
  nontrivial : ψ ≠ 1

theorem isPrincipalInvariantAddChar_one :
    IsPrincipalInvariantAddChar F (1 : AddChar (AdeleRing (𝓞 F) F) ℂ) :=
  fun _ => rfl

theorem not_isGlobalAddChar_one :
    ¬ IsGlobalAddChar F (1 : AddChar (AdeleRing (𝓞 F) F) ℂ) :=
  fun h => h.nontrivial rfl

def whittakerCoefficient (pins : CarrierPins F) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (α : F) (g : AdelicGL2 (𝓞 F) F) : ℂ :=
  letI := pins.nS
  ∫ x, φ (unipotentGL2 x * g) * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) α * x)) ∂pins.ν

def WhittakerCoefficientIntegrable (pins : CarrierPins F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ) (α : F)
    (g : AdelicGL2 (𝓞 F) F) : Prop :=
  letI := pins.nS
  Integrable
    (fun x => φ (unipotentGL2 x * g) * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) α * x))) pins.ν

@[simp] theorem whittakerCoefficient_zero (pins : CarrierPins F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (α : F) (g : AdelicGL2 (𝓞 F) F) :
    whittakerCoefficient F pins ψ (fun _ => (0 : ℂ)) α g = 0 := by
  simp only [whittakerCoefficient, zero_mul, integral_zero]

theorem whittakerCoefficient_zero_eq_constantTerm (pins : CarrierPins F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (g : AdelicGL2 (𝓞 F) F) :
    whittakerCoefficient F pins ψ φ 0 g
      = @constantTerm _ pins.nS _ _ pins.ν unipotentGL2 φ g := by
  simp only [whittakerCoefficient, map_zero, zero_mul, neg_zero, AddChar.map_zero_eq_one,
    mul_one]
  rfl

end AutomorphicForm

end
