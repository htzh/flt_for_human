/-
  The central character of a genuine smooth cusp realization.

  A smooth cusp realization `R` of a Hecke eigensystem `Φ` carries a central character
  `R.centralChar` on the idèles. Under the genuineness hypothesis — `R.toFun` continuous — this
  character is an idèle-class character (`IsIdeleClassChar`, trivial on the diagonal `Kˣ`), it admits
  the level of `Φ` as a modulus (`HeckeCharacter.AdmitsModulus`), and it is continuous. The first two
  conclusions hold for every smooth cusp realization; continuity is where `IsGenuineCuspRealizationAt`
  enters.

  Transcribed whole from the pin's proof file
  `P2M/Sol/S_AutomorphicForm_SmoothCuspRealizationAt_isIdeleClassChar_and_admitsModulus_level_and_continuous_of_genuine.lean`
  (pinned `aa2d8b3`, 199 lines / 15 declarations: the headline and its fourteen `private` helpers) and
  its statement from the wrapper
  `Theorems/Thm_AutomorphicForm_SmoothCuspRealizationAt_isIdeleClassChar_and_admitsModulus_level_and_continuous_of_genuine.lean`.

  Two of the pin's helpers — `globalPoints_scalar` (pin `:39`) and `continuous_centralScalar` (pin
  `:62`) — are already in the port with byte-identical statements, at
  `AutomorphicForm/Adelic/LsXiCharacter.lean:41` and `:49`; they are imported (this module adds that
  import to the two the manager wrote) rather than re-proved, so this file carries the remaining
  twelve helper blocks plus the headline.

  Surface. The pin keeps all fourteen helpers in the `CentralCharacterOfRealization` namespace and every
  one of them `private`; the port states the twelve transcribed ones publicly in
  `AutomorphicForm.SmoothCuspRealizationAt.CentralCharacterOfRealization`, because `check_port` reads
  each of the twelve as `ok` against the pin (the checked statement slice begins after the
  declaration's name, so the `private` modifier is not part of what is diffed and promotion changes
  nothing but visibility).  `centralScalar_mul_comm` is one fact stated in five modules; its one home
  is now `AutomorphicForm.centralScalar_mul_comm` in `Adelic/Basic.lean` (next to `centralScalar`
  itself), and the declarations that this module's wire and the Siegel modules' wires name are
  one-application restatements of it (AF dedup wave).

  spec-pin: Theorems/Thm_AutomorphicForm_SmoothCuspRealizationAt_isIdeleClassChar_and_admitsModulus_level_and_continuous_of_genuine.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_SmoothCuspRealizationAt_isIdeleClassChar_and_admitsModulus_level_and_continuous_of_genuine.lean
-/
import FLTForHuman.AutomorphicForm.Adelic.ProductionPinsGeneral
import FLTForHuman.HeckeCharacter.FiniteOrder
import FLTForHuman.AutomorphicForm.Adelic.LsXiCharacter

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.AdelicLevel

noncomputable section

namespace AutomorphicForm

namespace SmoothCuspRealizationAt

namespace CentralCharacterOfRealization

variable {F : Type} [Field F] [NumberField F]

noncomputable abbrev blockPins (D : Set (AdelicGL2 (𝓞 F) F)) (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (B : Set (AdeleRing (𝓞 F) F)) : CarrierPins F :=
  productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) gen B

noncomputable abbrev fullChar {D : Set (AdelicGL2 (𝓞 F) F)} {gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F}
    {B : Set (AdeleRing (𝓞 F) F)} {Φ : HeckeEigensystem F ℂ} (R : SmoothCuspRealizationAt F (blockPins D gen B) Φ) :
    (AdeleRing (𝓞 F) F)ˣ →* ℂˣ :=
  R.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom

variable {D : Set (AdelicGL2 (𝓞 F) F)} {gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F}
  {B : Set (AdeleRing (𝓞 F) F)} {Φ : HeckeEigensystem F ℂ}

theorem fullChar_apply (R : SmoothCuspRealizationAt F (blockPins D gen B) Φ) (z : (AdeleRing (𝓞 F) F)ˣ)
    {g : AdelicGL2 (𝓞 F) F} (hg : R.toFun g ≠ 0) :
    ((fullChar R z : ℂˣ) : ℂ) = R.toFun (centralScalar (𝓞 F) F z * g) / R.toFun g :=
  R.centralChar_apply_eq (Subgroup.topEquiv.symm z) hg

/-- Wire restatement of `AutomorphicForm.centralScalar_mul_comm` (`AutomorphicForm/Adelic/Basic.lean`,
the one home of the fact): this module's `spec-pin:` file names it here, so the name stays; the
proof is one application. -/
theorem centralScalar_mul_comm (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F) :
    centralScalar (𝓞 F) F z * g = g * centralScalar (𝓞 F) F z :=
  AutomorphicForm.centralScalar_mul_comm z g

theorem isIdeleClassChar (R : SmoothCuspRealizationAt F (blockPins D gen B) Φ) :
    IsIdeleClassChar (𝓞 F) F (fullChar R) := by
  intro a
  obtain ⟨g₀, hg₀⟩ := R.exists_ne_zero
  apply Units.ext
  rw [Units.val_one]
  refine (fullChar_apply R _ hg₀).trans ?_
  change R.toFun (centralScalar (𝓞 F) F (Units.map (algebraMap F (AdeleRing (𝓞 F) F)) a) * g₀)
    / R.toFun g₀ = 1
  rw [← globalPoints_scalar F a, R.left_invariant, div_self hg₀]

theorem continuous_fullChar (R : SmoothCuspRealizationAt F (blockPins D gen B) Φ)
    (hR : IsGenuineCuspRealizationAt F (blockPins D gen B) Φ R) : Continuous (fullChar R) := by
  have hRc : Continuous R.toFun := hR
  obtain ⟨g₀, hg₀⟩ := R.exists_ne_zero
  have hval : Continuous fun z : (AdeleRing (𝓞 F) F)ˣ => ((fullChar R z : ℂˣ) : ℂ) := by
    have h : (fun z : (AdeleRing (𝓞 F) F)ˣ => ((fullChar R z : ℂˣ) : ℂ))
        = fun z => R.toFun (centralScalar (𝓞 F) F z * g₀) / R.toFun g₀ := by
      funext z
      exact fullChar_apply R z hg₀
    rw [h]
    exact (hRc.comp ((continuous_centralScalar F).mul continuous_const)).div_const _
  refine Units.continuous_iff.mpr ⟨hval, ?_⟩
  have h : (fun z : (AdeleRing (𝓞 F) F)ˣ => ((fullChar R z)⁻¹ : ℂˣ).val)
      = (fun z : (AdeleRing (𝓞 F) F)ˣ => ((fullChar R z : ℂˣ) : ℂ)) ∘ (fun z => z⁻¹) := by
    funext z
    simp only [Function.comp_apply, map_inv]
  rw [h]
  exact hval.comp continuous_inv

def IsLevelUnit (N : Ideal (𝓞 F)) (u : (AdeleRing (𝓞 F) F)ˣ) : Prop :=
  (u : AdeleRing (𝓞 F) F).1 = 1 ∧
    ∀ v : HeightOneSpectrum (𝓞 F),
      Valued.v ((u : AdeleRing (𝓞 F) F).2 v) = 1 ∧
        Valued.v ((u : AdeleRing (𝓞 F) F).2 v - 1) ≤ idealBound (𝓞 F) N v

theorem inv_snd_apply (u : (AdeleRing (𝓞 F) F)ˣ) (v : HeightOneSpectrum (𝓞 F)) :
    ((u⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v = (((u : AdeleRing (𝓞 F) F).2 v)⁻¹ : v.adicCompletion F) := by
  have h : ((u : AdeleRing (𝓞 F) F).2 v) * (((u⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v) = 1 :=
    congrArg (fun x : AdeleRing (𝓞 F) F => x.2 v) u.mul_inv
  exact eq_inv_of_mul_eq_one_right h

theorem isLevelUnit_inv {N : Ideal (𝓞 F)} {u : (AdeleRing (𝓞 F) F)ˣ} (hu : IsLevelUnit N u) :
    IsLevelUnit N u⁻¹ := by
  obtain ⟨h1, h2⟩ := hu
  refine ⟨?_, fun v => ?_⟩
  · have h : (u : AdeleRing (𝓞 F) F).1 * ((u⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 = 1 :=
      congrArg (fun x : AdeleRing (𝓞 F) F => x.1) u.mul_inv
    rwa [h1, one_mul] at h
  · obtain ⟨hv1, hv2⟩ := h2 v
    rw [inv_snd_apply]
    refine ⟨by rw [map_inv₀, hv1, inv_one], ?_⟩
    have hne : (u : AdeleRing (𝓞 F) F).2 v ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hv1
      exact zero_ne_one hv1
    have hrw : ((u : AdeleRing (𝓞 F) F).2 v)⁻¹ - 1 = ((u : AdeleRing (𝓞 F) F).2 v)⁻¹ * (1 - (u : AdeleRing (𝓞 F) F).2 v) := by
      rw [mul_sub, mul_one, inv_mul_cancel₀ hne]
    rw [hrw, map_mul, map_inv₀, hv1, inv_one, one_mul, Valuation.map_sub_swap]
    exact hv2

theorem isLevelOneMatrix_of_isLevelUnit {N : Ideal (𝓞 F)} {u : (AdeleRing (𝓞 F) F)ˣ} (hu : IsLevelUnit N u) :
    IsLevelOneMatrix (𝓞 F) F N
      (glFin (𝓞 F) F (centralScalar (𝓞 F) F u) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) := by
  have hentry : ∀ i j : Fin 2,
      (glFin (𝓞 F) F (centralScalar (𝓞 F) F u) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j
        = (Matrix.diagonal (fun _ : Fin 2 => (u : AdeleRing (𝓞 F) F)) i j).2 := fun _ _ => rfl
  refine ⟨⟨fun i j => ?_, ?_⟩, ?_⟩
  · rw [hentry]
    by_cases h : i = j
    · subst h
      rw [Matrix.diagonal_apply_eq]
      exact fun v => le_of_eq (hu.2 v).1
    · rw [Matrix.diagonal_apply_ne _ h]
      exact zero_mem_integralFiniteAdeles
  · rw [hentry, Matrix.diagonal_apply_ne _ (by decide : (1 : Fin 2) ≠ 0)]
    exact fun v => by
      rw [show ((0 : AdeleRing (𝓞 F) F).2 : FiniteAdeleRing (𝓞 F) F) v = 0 from rfl, Valuation.map_zero]
      exact zero_le
  · rw [hentry, Matrix.diagonal_apply_eq]
    exact fun v => by
      rw [coe_sub_apply, coe_one_apply]
      exact (hu.2 v).2

theorem centralScalar_mem_level {u : (AdeleRing (𝓞 F) F)ˣ} (hu : IsLevelUnit Φ.level u) :
    centralScalar (𝓞 F) F u ∈ (blockPins D gen B : CarrierPins F).U Φ.level := by
  show centralScalar (𝓞 F) F u ∈ levelOne (𝓞 F) F Φ.level ⊓ finiteAdelicGL2Subgroup F
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [mem_levelOne_iff, mem_finiteLevelOne_iff]
    refine ⟨isLevelOneMatrix_of_isLevelUnit hu, ?_⟩
    rw [← map_inv, ← map_inv]
    exact isLevelOneMatrix_of_isLevelUnit (isLevelUnit_inv hu)
  · rw [mem_finiteAdelicGL2Subgroup_iff]
    have harch : ∀ i j : Fin 2,
        (glArch (𝓞 F) F (centralScalar (𝓞 F) F u) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j
          = (Matrix.diagonal (fun _ : Fin 2 => (u : AdeleRing (𝓞 F) F)) i j).1 := fun _ _ => rfl
    apply Units.ext
    rw [Units.val_one]
    ext i j
    rw [harch]
    by_cases h : i = j
    · subst h
      rw [Matrix.diagonal_apply_eq, hu.1, Matrix.one_apply_eq]
    · rw [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]
      rfl

theorem admitsModulus (R : SmoothCuspRealizationAt F (blockPins D gen B) Φ) :
    HeckeCharacter.AdmitsModulus F (fullChar R) Φ.level := by
  intro u hu1 hu2
  have hu : IsLevelUnit Φ.level u := by
    refine ⟨hu1, fun v => ⟨(hu2 v).1, ?_⟩⟩
    rw [idealBound_of_ne_bot Φ.level_ne_bot]
    exact (hu2 v).2
  obtain ⟨g₀, hg₀⟩ := R.exists_ne_zero
  apply Units.ext
  rw [Units.val_one, fullChar_apply R u hg₀, centralScalar_mul_comm,
    R.level_invariant g₀ _ (centralScalar_mem_level hu), div_self hg₀]

end CentralCharacterOfRealization

end SmoothCuspRealizationAt

theorem SmoothCuspRealizationAt.isIdeleClassChar_and_admitsModulus_level_and_continuous_of_genuine
    (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F)) (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (B : Set (AdeleRing (𝓞 F) F)) (Φ : HeckeEigensystem F ℂ)
    (R : SmoothCuspRealizationAt F
      (productionPinsOf F D (fun N => NumberField.AdelicLevel.levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        gen B) Φ) :
    IsIdeleClassChar (𝓞 F) F (R.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom) ∧
      HeckeCharacter.AdmitsModulus F (R.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom) Φ.level ∧
      (IsGenuineCuspRealizationAt F
          (productionPinsOf F D (fun N => NumberField.AdelicLevel.levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
            gen B) Φ R →
        Continuous (R.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom)) :=
  ⟨CentralCharacterOfRealization.isIdeleClassChar R,
    CentralCharacterOfRealization.admitsModulus R,
    CentralCharacterOfRealization.continuous_fullChar R⟩

end AutomorphicForm

end
