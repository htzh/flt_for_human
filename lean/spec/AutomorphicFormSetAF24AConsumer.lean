/-
  Cross-module wire test for SET-AF24A (the `𝔰𝔩₂`-string decomposition at a complex place).

  A `spec/` probe, not a library module. Two zones, over a general `F` with a complex place `w`
  plus one instantiation at `F = ℚ`, reading the three headlines of `Adelic/Su2Strings.lean`
  against each other and against the ported engines
  `Adelic/ArchDerivCasimirComplexAPI.lean` (`archDerivAtComplex_const`,
  `isArchSmoothAtComplex_const`) and `LinearAlgebra/Eigenspace/Sl2Strings.lean` (the string-basis
  engine the 908 headline applies, whose `LinearIndependent.ne_zero` is what kills the index).

  * `bot_wire` is the shared brick: the zero submodule `⊥` satisfies the three side conditions
    the headlines carry (`FiniteDimensional`, complex smoothness, right-`K`-invariance). It is the
    only degenerate `Y` on which `hYs` is free;
  * `su2Strings_bot_index_eq_zero` is the 908 headline at `Y = ⊥`: the string basis of the zero
    space has **no** strings, `m = 0` — read off its `LinearIndependent` conjunct, since a
    non-zero index would exhibit a nonzero member of `⊥`;
  * `hasArchCharacter_zero_of_mem_bot` is the 169 headline at `Y = ⊥`: every vector of `⊥` is the
    zero function, and the three vanishing derivatives come from the engine's
    `archDerivAtComplex_const`. The trivial archimedean character is the conclusion;
  * `decomposition_and_char` composes the two big headlines: the 755 weight-decomposition conjunct
    and the 169 character conclusion for the same `x` from one hypothesis bundle;
  * `hasArchCharacter_zero_rat` reads 169 at the concrete `F = ℚ` / `AdelicGL2 (𝓞 ℚ) ℚ`. Every
    place of `ℚ` is real, so the hypothesis `hw : w.IsComplex` has no inhabitant — the statement
    still elaborates, which is the part of a wire that a vacuous instantiation tests.

  It imports only the modules it composes.
-/
import FLTForHuman.AutomorphicForm.Adelic.Su2Strings
import FLTForHuman.AutomorphicForm.Adelic.ArchDerivCasimirComplexAPI
import FLTForHuman.LinearAlgebra.Eigenspace.Sl2Strings

set_option autoImplicit false

noncomputable section

open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open AutomorphicForm AutomorphicForm.Su2Strings

namespace SetAF24ASu2StringsConsumer

variable {F : Type} [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsComplex)

/-- **The shared brick.** The zero submodule carries the three side conditions of the SET-AF24
headlines: it is finite-dimensional, every one of its vectors is complex-smooth (it is `0`), and it
is preserved by right translation by a row isometry. -/
theorem bot_wire :
    (∀ y ∈ (⊥ : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)), IsArchSmoothAtComplex hw y) ∧
    (∀ (k : rowIsometrySubgroup₀ w.Completion),
      ∀ y ∈ (⊥ : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)),
        (fun g => y (g * rowIsometryInclAt₀ F w k)) ∈
          (⊥ : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))) := by
  constructor
  · intro y hy
    rw [Submodule.mem_bot] at hy
    rw [hy]
    exact isArchSmoothAtComplex_const hw 0
  · intro k y hy
    rw [Submodule.mem_bot] at hy
    rw [hy]
    exact Submodule.zero_mem (⊥ : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))

/-- **The 908 headline at `Y = ⊥`.** The string basis of the zero space is empty: the number of
highest weights is `m = 0`. A nonzero `m` would give a nonzero member of `⊥` through the
`LinearIndependent` conjunct. -/
theorem su2Strings_bot_index_eq_zero :
    ∃ (m : ℕ) (n : Fin m → ℕ) (x : Fin m → ℕ → (AdelicGL2 (𝓞 F) F → ℂ)),
      m = 0 ∧ (∀ s p, x s p ∈ (⊥ : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))) ∧
      (∀ s (p : ℕ), p ≤ n s → HasCircleWeightAt hw ((n s : ℤ) - 2 * (p : ℤ)) (x s p)) := by
  obtain ⟨hYs, hYK⟩ := bot_wire hw
  obtain ⟨m, n, x, hxY, -, hli, -, -, -, -, hcw⟩ :=
    exists_su2Strings_of_finiteDimensional_of_isArchSmoothAtComplex F hw
      (⊥ : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) hYs hYK
  refine ⟨m, n, x, ?_, hxY, hcw⟩
  by_contra hm
  have hpos : 0 < m := Nat.pos_of_ne_zero hm
  have hmem : x ⟨0, hpos⟩ 0 = 0 := by
    have h0 := hxY ⟨0, hpos⟩ 0
    rwa [Submodule.mem_bot] at h0
  exact hli.ne_zero ⟨⟨0, hpos⟩, ⟨0, Nat.succ_pos _⟩⟩ hmem

/-- **The 169 headline at `Y = ⊥`.** A vector of the zero submodule is the zero function, whose
three archimedean derivatives vanish by the engine's `archDerivAtComplex_const`; the conclusion is
that it is of trivial archimedean character at weight one. -/
theorem hasArchCharacter_zero_of_mem_bot (hw : w.IsComplex) (x : AdelicGL2 (𝓞 F) F → ℂ)
    (hx : x ∈ (⊥ : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))) :
    HasArchCharacterAt₀ F w 1 x := by
  obtain ⟨hYs, hYK⟩ := bot_wire hw
  have hx0 : x = 0 := by rwa [Submodule.mem_bot] at hx
  rw [hx0]
  refine hasArchCharacterAtZero_one_of_archDerivAtComplex_compact_eq_zero F hw
    (⊥ : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) hYs hYK 0 (Submodule.zero_mem _) ?_ ?_ ?_
  · exact archDerivAtComplex_const hw .iH (0 : ℂ)
  · change archDerivAtComplex hw .Fm (fun _ => (0 : ℂ)) -
      archDerivAtComplex hw .E (fun _ => (0 : ℂ)) = (fun _ => (0 : ℂ))
    rw [archDerivAtComplex_const, archDerivAtComplex_const]
    funext g
    simp
  · change archDerivAtComplex hw .iE (fun _ => (0 : ℂ)) +
      archDerivAtComplex hw .iFm (fun _ => (0 : ℂ)) = (fun _ => (0 : ℂ))
    rw [archDerivAtComplex_const, archDerivAtComplex_const]
    funext g
    simp

/-- **The two big headlines composed.** A vector of a finite-dimensional `Y` killed by the three
derivatives has both the 755 circle-weight decomposition and the 169 trivial archimedean
character, from one hypothesis bundle. -/
theorem decomposition_and_char
    (Y : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) [FiniteDimensional ℂ Y]
    (hYs : ∀ y ∈ Y, IsArchSmoothAtComplex hw y)
    (hYK : ∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ y ∈ Y,
      (fun g => y (g * rowIsometryInclAt₀ F w k)) ∈ Y)
    (x : AdelicGL2 (𝓞 F) F → ℂ) (hx : x ∈ Y)
    (h0 : archDerivAtComplex hw .iH x = 0)
    (h1 : archDerivAtComplex hw .Fm x - archDerivAtComplex hw .E x = 0)
    (h2 : archDerivAtComplex hw .iE x + archDerivAtComplex hw .iFm x = 0) :
    (∃ (ms : Finset ℤ) (ys : ℤ → (AdelicGL2 (𝓞 F) F → ℂ)),
      (∀ m ∈ ms, ys m ∈ Y ∧ HasCircleWeightAt hw m (ys m) ∧
        archDerivAtComplex hw .iH (ys m) = (Complex.I * (m : ℂ)) • ys m) ∧
      x = ∑ m ∈ ms, ys m) ∧
    HasArchCharacterAt₀ F w 1 x := by
  obtain ⟨-, -, -, hdec⟩ :=
    su2Derivs_stable_and_hasDerivAt_and_exists_sum_hasCircleWeightAt_of_finiteDimensional
      F hw Y hYs hYK
  exact ⟨hdec x hx,
    hasArchCharacterAtZero_one_of_archDerivAtComplex_compact_eq_zero F hw Y hYs hYK x hx h0 h1 h2⟩

/-- **The 169 headline at `F = ℚ`.** Every place of `ℚ` is real, so `hw : w.IsComplex` is
uninhabited and this is vacuously true; the content the wire tests is that the concrete
`AdelicGL2 (𝓞 ℚ) ℚ` instance of the three-hypothesis statement elaborates and is discharged by
the zero-function corollary above. -/
theorem hasArchCharacter_zero_rat (w : InfinitePlace ℚ) (hw : w.IsComplex) :
    HasArchCharacterAt₀ ℚ w 1 (fun _ => 0) :=
  hasArchCharacter_zero_of_mem_bot hw 0 (Submodule.zero_mem _)

end SetAF24ASu2StringsConsumer
