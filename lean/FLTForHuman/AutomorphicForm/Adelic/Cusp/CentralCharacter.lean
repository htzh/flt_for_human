/-
  The central character is determined away from finitely many places.

  Two smooth cusp realizations over the same production pins whose eigensystems agree away from
  finitely many places have the same central character. It is the comparison that lets the
  compact-cusp notion's realization be identified with the arithmetic one.

  Transcribed from
  `P2M/Sol/S_AutomorphicForm_SmoothCuspRealizationAt_centralChar_eq_of_agreesAwayFromFinite.lean`
  (pinned `aa2d8b3`, 113 lines). The pin's search-stage namespace `CCEE4` is renamed to the
  subject sub-namespace `CentralChar`; the row stays at the module's namespace.

  Heartbeat probe: silent at `-DmaxHeartbeats=50000`, first failure at `20000`
  (`timeout at whnf`, line 77, the row's opening). No in-file floor (the pin's
  `set_option maxHeartbeats 1600000` / `synthInstance.maxHeartbeats 1600000` are *not* carried).

  ## Port deltas

  * `AutomorphicForm/Adelic/Cusp/RealizationTwist` — added for
    `AutomorphicForm.TwistRpow.det_diagOne`, the port's copy used in the proof of `det_diagOne`
    (the pin reaches it through its `Definitions`/`Theorems` closure).

  spec-pin: P2M/Sol/S_AutomorphicForm_SmoothCuspRealizationAt_centralChar_eq_of_agreesAwayFromFinite.lean
-/
import FLTForHuman.AutomorphicForm.Adelic.Cusp.CompactCuspNotion
import FLTForHuman.AutomorphicForm.Adelic.Cusp.RealizationTwist
import FLTForHuman.AutomorphicForm.Adelic.ProductionPinsGeneral
import FLTForHuman.AutomorphicForm.Adelic.Cusp.GenuineRealization
import FLTForHuman.HeckeCharacter.Equality

set_option autoImplicit false

noncomputable section

open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar MeasureTheory
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

namespace AutomorphicForm.SmoothCuspRealizationAt

namespace CentralChar

open IsDedekindDomain

theorem det_diagOne {A : Type*} [CommRing A] (a : Aˣ) :
    Matrix.GeneralLinearGroup.det (NumberField.AdelicLevel.diagOne a) = a :=
  AutomorphicForm.TwistRpow.det_diagOne a

theorem det_heckeGen (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v)
      = Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v (uniformizerUnit K v)) := by
  show Matrix.GeneralLinearGroup.det (heckeGenAt (𝓞 K) K v (uniformizerUnit K v)) = _
  unfold heckeGenAt
  simp only [MonoidHom.coe_comp, Function.comp_apply]
  exact det_diagOne _

theorem isLsXiFunction_of_realization {F : Type} [Field F] [NumberField F] (pins : CarrierPins F)
    (Φ : HeckeEigensystem F ℂ) (R : SmoothCuspRealizationAt F pins Φ) :
    IsLsXiFunction (𝓞 F) F pins.Z R.centralChar R.toFun := by
  have h := R.smoothCusp.1.1
  unfold IsAutomorphicFnAt at h
  exact ((@lsXiMemberAt_iff (𝓞 F) F _ _ _ _ _ pins.mS pins.μ pins.Z R.centralChar pins.D R.toFun).mp h).1

theorem centralChar_det_gen (K : Type) [Field K] [NumberField K] (D : Set (AdelicGL2 (𝓞 K) K))
    (Φ : HeckeEigensystem K ℂ)
    (R : SmoothCuspRealizationAt K
      (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) Φ)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ R.exceptionalSet) :
    ((R.centralChar ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) = Φ.b v := by
  obtain ⟨g₀, hg₀⟩ := R.exists_ne_zero
  have h1 := R.central_eigen v hv g₀

  have hls := isLsXiFunction_of_realization _ _ R
  have h2 := hls.central_transform ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ g₀

  have h3 : ((R.centralChar ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) * R.toFun g₀
      = Φ.b v * R.toFun g₀ := by
    rw [← h2]; exact h1
  exact mul_right_cancel₀ hg₀ h3

end CentralChar

theorem centralChar_eq_of_agreesAwayFromFinite
    (K : Type) [Field K] [NumberField K] (D : Set (AdelicGL2 (𝓞 K) K))
    (Θ Θ' : HeckeEigensystem K ℂ)
    (hΘ : Θ.AgreesAwayFromFinite Θ')
    (R : SmoothCuspRealizationAt K
      (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
      Θ.toRawCentral)
    (hR : IsGenuineCuspRealizationAt K
      (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
      Θ.toRawCentral R)
    (R' : SmoothCuspRealizationAt K
      (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
      Θ'.toRawCentral)
    (hR' : IsGenuineCuspRealizationAt K
      (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
      Θ'.toRawCentral R') :
    R.centralChar = R'.centralChar := by
  classical

  obtain ⟨hic₁, hmod₁, hc₁⟩ :=
    AutomorphicForm.SmoothCuspRealizationAt.isIdeleClassChar_and_admitsModulus_level_and_continuous_of_genuine
      K D (fun v => heckeGen (𝓞 K) K v) (adelicBox K) Θ.toRawCentral R
  obtain ⟨hic₂, hmod₂, hc₂⟩ :=
    AutomorphicForm.SmoothCuspRealizationAt.isIdeleClassChar_and_admitsModulus_level_and_continuous_of_genuine
      K D (fun v => heckeGen (𝓞 K) K v) (adelicBox K) Θ'.toRawCentral R'
  obtain ⟨S₀, hS₀⟩ := hΘ.toRawCentral
  have key := HeckeCharacter.eq_of_forall_apply_localUnit_uniformizerUnit_eq K
    (R.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom) (R'.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom)
    hic₁ hic₂ (hc₁ hR) (hc₂ hR') _ _ hmod₁ hmod₂ (S₀ ∪ R.exceptionalSet ∪ R'.exceptionalSet) (by
      intro v hv
      simp only [Finset.mem_union, not_or] at hv
      obtain ⟨⟨hv0, hv1⟩, hv2⟩ := hv
      apply Units.ext
      rw [← CentralChar.det_heckeGen]
      simp only [MonoidHom.coe_comp, Function.comp_apply]
      have e1 := CentralChar.centralChar_det_gen K D Θ.toRawCentral R v hv1
      have e2 := CentralChar.centralChar_det_gen K D Θ'.toRawCentral R' v hv2
      have e3 : Θ.toRawCentral.b v = Θ'.toRawCentral.b v := (hS₀ v hv0).2
      convert e1.trans (e3.trans e2.symm) using 2
      rfl
      rfl)

  ext z
  have := congrArg (fun χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ => ((χ (z : (AdeleRing (𝓞 K) K)ˣ) : ℂˣ) : ℂ)) key
  simp at this
  exact this

end AutomorphicForm.SmoothCuspRealizationAt

end
