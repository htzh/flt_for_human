/-
  The global additive character of a number field: principal invariance, continuity, and
  nontriviality.

  An additive character `ψ` of the adèle ring `𝔸_F` is *principal invariant* when it is
  trivial on the diagonal image of `F` (`IsPrincipalInvariantAddChar`), and a *global* additive
  character when it is principal invariant, continuous and nontrivial (`IsGlobalAddChar`).
  The standard character `stdAddChar F` of `NumberField/AdelicTraceFin.lean` is the model: it
  is continuous, trivial on the principal adèles and nontrivial (`isGlobalAddChar_stdAddChar`
  territory), and every statement about a Whittaker coefficient takes such a `ψ` as a
  hypothesis.

  The two degenerate cases are recorded here as well: the trivial character is principal
  invariant, and it is not a global additive character.

  These four declarations are the character-theoretic half of the pin's
  `Definitions/Def_AutomorphicForm_WhittakerCoefficient.lean` (pinned `aa2d8b3`, lines 15–29);
  the Whittaker coefficient itself is the other half of the same pin file and is stated
  against these predicates. The split is by subject: a predicate on a character of the adèle
  ring is a number-field object that the standard-character developments and the coefficient
  both sit above, while the coefficient is the analytic object of the automorphic
  development. The pin filed the two together because the pipeline did.

  spec-pin: Definitions/Def_AutomorphicForm_WhittakerCoefficient.lean
-/
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.Algebra.Group.AddChar

set_option autoImplicit false

open IsDedekindDomain NumberField

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

end AutomorphicForm

end
