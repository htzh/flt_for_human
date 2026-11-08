/-
  Consumer zone for `FLTForHuman/AutomorphicForm/Adelic/Cusp/GenuineRealization.lean`.

  The headline is exercised in composition, never by `#check`: its three conclusions are consumed by
  the twist layer (`AutomorphicForm/Adelic/FnTwist.lean`) and by the `HeckeCharacter` modulus
  vocabulary, on the same realization `R` that the module quantifies over.

  * the **idèle-class** half (`(⋯_of_genuine F D gen B Φ R).1`, an `IsIdeleClassChar` of `fullChar R`)
    is fed to `chiDet_globalPoints_mul` and composed with `SmoothCuspRealizationAt.left_invariant` to
    give the left-invariance of the twist under `GL₂(K)`. The twist `fnTwist F η φ` is `χ(det g) · φ g`,
    so `φ`'s invariance under `GL₂(K)` survives it exactly because `η` is trivial on the diagonal `Kˣ`:
    `globalPoints γ` shifts `det` by a norm, which `chiDet` can absorb only on the image of `Kˣ`;
  * the **genuineness** half (`(⋯_of_genuine F D gen B Φ R).2.2 hgen`, a `Continuous (fullChar R)`) is
    composed with `Units.continuous_val.matrix_det` to make `chiDet (𝓞 F) F (fullChar R)` continuous,
    hence `fnTwist F (fullChar R) R.toFun` continuous when `R` is genuine: the twist of a genuine
    realization is again a genuine section, not merely an invariant one;
  * the **modulus** half (`(⋯_of_genuine F D gen B Φ R).2.1`, a `HeckeCharacter.AdmitsModulus` at
    `Φ.level`) is composed with `idealBound_of_ne_bot` to read the conclusion at the module's own
    `IsLevelUnit` predicate (which is why that helper is part of the promoted surface), and with
    `twistedCentralChar` to show that the character of the twist admits the same level.

  `spec/` is outside every Lake library, so this file is checked by
  `lake env lean spec/AutomorphicFormSetAF34BConsumer.lean` and never enters the build.
-/
import FLTForHuman.AutomorphicForm.Adelic.Cusp.GenuineRealization
import FLTForHuman.AutomorphicForm.Adelic.FnTwist

set_option autoImplicit false

noncomputable section

open IsDedekindDomain NumberField NumberField.AdelicLevel
open AutomorphicForm

namespace AutomorphicFormSetAF34BConsumer

variable {F : Type} [Field F] [NumberField F]
variable {D : Set (AdelicGL2 (𝓞 F) F)} {gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F}
  {B : Set (AdeleRing (𝓞 F) F)} {Φ : HeckeEigensystem F ℂ}

/-- The pins the headline is stated at. -/
abbrev pinsOf : CarrierPins F :=
  productionPinsOf F D
    (fun N => NumberField.AdelicLevel.levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) gen B

/-- `R.centralChar` read on the idèles through `(⊤ : Subgroup (𝔸)ˣ) ≃* (𝔸)ˣ` — the character the
headline's three conclusions are about. -/
def fullChar (R : SmoothCuspRealizationAt F (pinsOf (F := F) (D := D) (gen := gen) (B := B)) Φ) :
    (AdeleRing (𝓞 F) F)ˣ →* ℂˣ :=
  R.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom

variable {R : SmoothCuspRealizationAt F (pinsOf (F := F) (D := D) (gen := gen) (B := B)) Φ}

/-- The headline at `R`, with the pins spelled as the wrapper spells them. -/
theorem headline :
    IsIdeleClassChar (𝓞 F) F (fullChar R) ∧
      HeckeCharacter.AdmitsModulus F (fullChar R) Φ.level ∧
      (IsGenuineCuspRealizationAt F (pinsOf (F := F) (D := D) (gen := gen) (B := B)) Φ R →
        Continuous (fullChar R)) :=
  SmoothCuspRealizationAt.isIdeleClassChar_and_admitsModulus_level_and_continuous_of_genuine
    F D gen B Φ R

/-- The twist of `R.toFun` by the central character is left-invariant under `GL₂(K)`: the
idèle-class conclusion is what lets `chiDet` absorb the `det (globalPoints γ) = algebraMap ‖det γ‖`
of a rational point. -/
theorem fnTwist_left_invariant (γ : GL (Fin 2) F) (g : AdelicGL2 (𝓞 F) F) :
    fnTwist F (fullChar R) R.toFun (globalPoints (𝓞 F) F γ * g)
      = fnTwist F (fullChar R) R.toFun g := by
  have hη : IsIdeleClassChar (𝓞 F) F (fullChar R) := (headline (R := R)).1
  simp only [fnTwist_apply]
  rw [chiDet_globalPoints_mul F (fullChar R) hη γ g, R.left_invariant]

/-- Under genuineness the twist is continuous: the second half of the headline supplies the continuity
of the character, and `det` is continuous on `GL₂(𝔸_F)`. -/
theorem continuous_fnTwist_of_genuine
    (hgen : IsGenuineCuspRealizationAt F (pinsOf (F := F) (D := D) (gen := gen) (B := B)) Φ R) :
    Continuous (fnTwist F (fullChar R) R.toFun) := by
  have hη : Continuous (fullChar R) := (headline (R := R)).2.2 hgen
  have hdet : Continuous (Matrix.GeneralLinearGroup.det :
      AdelicGL2 (𝓞 F) F → (AdeleRing (𝓞 F) F)ˣ) := by
    refine Units.continuous_iff.mpr ⟨?_, ?_⟩
    · show Continuous fun g : AdelicGL2 (𝓞 F) F =>
        ((Matrix.GeneralLinearGroup.det g : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)
      simpa only [Matrix.GeneralLinearGroup.val_det_apply] using Units.continuous_val.matrix_det
    · show Continuous fun g : AdelicGL2 (𝓞 F) F =>
        (((Matrix.GeneralLinearGroup.det g)⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)
      simpa only [← map_inv, Matrix.GeneralLinearGroup.val_det_apply] using
        Units.continuous_coe_inv.matrix_det
  have hχ : Continuous (chiDet (𝓞 F) F (fullChar R)) := Units.continuous_val.comp (hη.comp hdet)
  have hφ : Continuous R.toFun := hgen
  have h : Continuous fun g => chiDet (𝓞 F) F (fullChar R) g * R.toFun g := hχ.mul hφ
  exact h

/-- The modulus conclusion read at the module's `IsLevelUnit` predicate: a unit that is `1` at the
archimedean places and level-`Φ.level`-congruent at the finite ones is killed by the central
character. `idealBound` is converted to `idealMultiplicity` — the shape `AdmitsModulus` states — only
through `idealBound_of_ne_bot`, using `Φ.level_ne_bot`. -/
theorem fullChar_eq_one_of_isLevelUnit {u : (AdeleRing (𝓞 F) F)ˣ}
    (hu : SmoothCuspRealizationAt.CentralCharacterOfRealization.IsLevelUnit Φ.level u) :
    fullChar R u = 1 :=
  (headline (R := R)).2.1 u hu.1 fun v => ⟨(hu.2 v).1, by
    have h := (hu.2 v).2
    rwa [idealBound_of_ne_bot Φ.level_ne_bot] at h⟩

/-- The central character of the twist `fnTwist F (fullChar R) R.toFun`: the port states it as
`twistedCentralChar F Z ξ η` at `Z = ⊤`, and there `ξ` and `η` are the same hom on the idèles, so it is
`fullChar R * fullChar R ^ 2` (`ξ · η²` at `ξ = η`). -/
def twistedFullChar : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ :=
  fullChar R * fullChar R ^ 2

/-- Twisting by an idèle-class character does not change the modulus: the twisted character is still
trivial on the level subgroup, because the headline's modulus conclusion already kills `fullChar R`
there and both factors of the twist are powers of it. -/
theorem twistedFullChar_admitsModulus :
    HeckeCharacter.AdmitsModulus F (twistedFullChar (R := R)) Φ.level := by
  have hmod : HeckeCharacter.AdmitsModulus F (fullChar R) Φ.level := (headline (R := R)).2.1
  intro u hu1 hu2
  have hu : fullChar R u = 1 := hmod u hu1 hu2
  unfold twistedFullChar
  rw [MonoidHom.mul_apply, MonoidHom.pow_apply, hu]
  simp

end AutomorphicFormSetAF34BConsumer
