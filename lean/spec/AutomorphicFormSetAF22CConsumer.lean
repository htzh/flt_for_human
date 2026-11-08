/-
  Cross-module wire test for SET-AF22C (the character of an `LsXi` function).

  A `spec/` probe, not a library module. **One zone**, and it reads both conjuncts of
  `AutomorphicForm.isIdeleClassChar_and_continuous_of_isLsXiFunction_of_continuous`:

  * `trivial_character` runs the headline at data the port can name without inventing anything —
    the trivial character `1` on the idèles and the constant function `1`, which is a continuous
    `IsLsXiFunction` for it (`⟨fun _ _ => rfl, fun _ _ => by simp⟩`) and nonzero, so `hne` holds —
    and then states the conclusion in the headline's own two conjuncts at that data. It dies if
    either conjunct, the hypothesis order, or the `⊤`-coercion shape changes.
  * `isIdeleClassChar_of_hypotheses` takes the headline's hypotheses as arguments and returns the
    first conjunct **as the definition** `IsIdeleClassChar` (at the character pulled back along
    `Subgroup.topEquiv.symm`, which is exactly the coercion `z ↦ ⟨z, Subgroup.mem_top z⟩`), together
    with the second conjunct verbatim. The proof is the headline itself, so the zone dies if either
    conjunct is restated. No pin data is assumed here beyond the headline's own hypotheses.

  It imports only the module it composes.
-/
import FLTForHuman.AutomorphicForm.Adelic.LsXiCharacter

set_option autoImplicit false

open MeasureTheory NumberField Matrix
open AutomorphicForm

noncomputable section

namespace SetAF22CCharacterConsumer

/-- **Zone A — the headline at the trivial character and the constant function `1`.** `φ ≡ 1` is
the nonzero companion of `isLsXiFunction_zero`: it is invariant under `GL₂(K)` and transforms by
the trivial character, and being constant it is continuous. The conclusion is the headline's two
conjuncts at that data. -/
theorem trivial_character (K : Type) [Field K] [NumberField K] :
    (∀ u : Kˣ, (1 : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
        ⟨Units.map (algebraMap K (AdeleRing (𝓞 K) K)) u, Subgroup.mem_top _⟩ = 1) ∧
      Continuous fun z : (AdeleRing (𝓞 K) K)ˣ =>
        (1 : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) ⟨z, Subgroup.mem_top z⟩ :=
  isIdeleClassChar_and_continuous_of_isLsXiFunction_of_continuous K 1 (fun _ => 1)
    ⟨fun _ _ => rfl, fun _ _ => by simp⟩ continuous_const ⟨1, one_ne_zero⟩

/-- **Zone A — the headline read as `IsIdeleClassChar` plus continuity.** With the headline's
hypotheses as arguments, the first conjunct becomes the definition `IsIdeleClassChar` of the
character pulled back from `⊤` to the idèles along `Subgroup.topEquiv.symm`, and the second
conjunct is the headline's own continuity statement. -/
theorem isIdeleClassChar_of_hypotheses
    (K : Type) [Field K] [NumberField K]
    (χ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (φ : AdelicGL2 (𝓞 K) K → ℂ)
    (hφ : IsLsXiFunction (𝓞 K) K ⊤ χ φ) (hcont : Continuous φ) (hne : ∃ g, φ g ≠ 0) :
    IsIdeleClassChar (𝓞 K) K
        (χ.comp ((Subgroup.topEquiv (G := (AdeleRing (𝓞 K) K)ˣ)).symm.toMonoidHom)) ∧
      Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => χ ⟨z, Subgroup.mem_top z⟩ := by
  obtain ⟨htriv, hcontχ⟩ :=
    isIdeleClassChar_and_continuous_of_isLsXiFunction_of_continuous K χ φ hφ hcont hne
  exact ⟨htriv, hcontχ⟩

end SetAF22CCharacterConsumer

end
