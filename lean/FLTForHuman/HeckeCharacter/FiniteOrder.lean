/-
  Finite-order Hecke characters: the modulus vocabulary.

  A Hecke character `χ` on the idèles of a number field `K` is of *finite order*
  when it is a continuous idèle-class character taking values in roots of unity;
  it *admits a modulus* `𝔣` when it is trivial on the idèles that are `1` at the
  archimedean places and multiplicatively congruent to `1` modulo `𝔣` at the
  finite places (`idealMultiplicity` is the exponent of a height-one prime in
  `𝔣`).

  The port's home of the pin's `Definitions/Def_HeckeCharacter_FiniteOrder.lean`
  (pinned `aa2d8b3`, 30 lines), transcribed verbatim and whole: the structure
  `IsFiniteOrderHeckeChar` and the two definitions `idealMultiplicity` and
  `AdmitsModulus`, at their pin names inside `namespace HeckeCharacter`.  The pin's
  single import `Definitions/Def_AutomorphicForm_AdelicLsXi` is the port's
  `AutomorphicForm/Adelic/LsXi.lean` (the pin file is split in the port, playbook
  §3.1).  Nothing is promoted, nothing is registered, no statement is changed:
  this is a new definition leaf with no dependents in the port.

  References (public mirror, pinned):
  <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_HeckeCharacter_FiniteOrder.lean>

  spec-pin: Definitions/Def_HeckeCharacter_FiniteOrder.lean
-/

import FLTForHuman.AutomorphicForm.Adelic.LsXi
import Mathlib.RingTheory.UniqueFactorizationDomain.FactorSet

set_option autoImplicit false

open NumberField AutomorphicForm IsDedekindDomain WithZero

noncomputable section

namespace HeckeCharacter

variable (K : Type*) [Field K] [NumberField K]

structure IsFiniteOrderHeckeChar (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) : Prop where
  isIdeleClassChar : IsIdeleClassChar (𝓞 K) K χ
  continuous : Continuous χ
  isOfFinOrder : IsOfFinOrder χ

def idealMultiplicity (v : HeightOneSpectrum (𝓞 K)) (𝔣 : Ideal (𝓞 K)) : ℕ :=
  (Associates.mk v.asIdeal).count (Associates.mk 𝔣).factors

def AdmitsModulus (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (𝔣 : Ideal (𝓞 K)) : Prop :=
  ∀ u : (AdeleRing (𝓞 K) K)ˣ,
    (u : AdeleRing (𝓞 K) K).1 = 1 →
    (∀ v : HeightOneSpectrum (𝓞 K),
      Valued.v ((u : AdeleRing (𝓞 K) K).2 v) = 1 ∧
      Valued.v ((u : AdeleRing (𝓞 K) K).2 v - 1)
        ≤ WithZero.exp (-(idealMultiplicity K v 𝔣 : ℤ))) →
    χ u = 1

end HeckeCharacter

end
