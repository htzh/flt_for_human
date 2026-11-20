/-
  The compact cusp notion via the ℤ[√-2] character.

  `viaCompactCuspNotion` is the cuspidality notion obtained by twisting a weight-one Hecke
  eigensystem along `iotaZsqrtdNegTwo : ℤ[√-2] →+* ℂ` and asking for a smooth cusp realization
  with weight-one archimedean character, holomorphic on the real places, and with the
  eigenvalues equal to `chiNegThree` away from finitely many places. It is the notion the
  compact-cusp route of the weight-one comparison uses, and `isArithCuspRealizableVia` records
  that its cusp forms are arithmetically realizable.

  Transcribed from `Definitions/Def_AutomorphicForm_ViaCompactCuspNotion.lean` (pinned
  `aa2d8b3`, 74 lines / 7 declarations). The pin's stub imports are replaced by the port
  modules; the pin namespace `AutomorphicForm` is kept.

  Heartbeat probe: silent at `-DmaxHeartbeats=500`, first failure at `200`
  (`timeout at isDefEq`, line 37, `iotaZsqrtdNegTwo`'s `sqrt`-side proof). No in-file floor.

  ## Port deltas

  None: the scaffold's imports suffice; the pin's `Mathlib` import is covered by the
  `UpperHalfPlane` modules plus the port's cusp layer.

  spec-pin: Definitions/Def_AutomorphicForm_ViaCompactCuspNotion.lean
-/
import FLTForHuman.AutomorphicForm.Adelic.Cusp.ArithRealization
import FLTForHuman.AutomorphicForm.Adelic.ProductionPinsCompact
import FLTForHuman.AutomorphicForm.Adelic.ArchWeightCharTransport
import FLTForHuman.ModularForms.WeightOne.EisensteinChiNegThree
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic

set_option autoImplicit false

noncomputable section

open IsDedekindDomain NumberField EisensteinWeightOne CongruenceSubgroup
open scoped Manifold

namespace AutomorphicForm

def iotaZsqrtdNegTwo : ℤ√(-2) →+* ℂ :=
  Zsqrtd.lift ⟨(Real.sqrt 2 : ℂ) * Complex.I, by
    have h2 : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
      rw [← Complex.ofReal_mul, ← Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2)]
      norm_num [Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2)]
    calc ((Real.sqrt 2 : ℂ) * Complex.I) * ((Real.sqrt 2 : ℂ) * Complex.I)
        = (((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ)) * (Complex.I * Complex.I) := by
          ring
      _ = ((-2 : ℤ) : ℂ) := by rw [h2, Complex.I_mul_I]; norm_num⟩

@[simp] theorem iotaZsqrtdNegTwo_apply (z : ℤ√(-2)) :
    iotaZsqrtdNegTwo z = (z.re : ℂ) + (z.im : ℂ) * ((Real.sqrt 2 : ℂ) * Complex.I) := by
  simp [iotaZsqrtdNegTwo, Zsqrtd.lift]

noncomputable def iwasawaSectionGL (z : UpperHalfPlane) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(z.im : ℝ), (z.re : ℝ); 0, 1] (by
    simp [Matrix.det_fin_two_of]
    exact z.im_ne_zero)

def IsArchHolomorphicAt {F : Type} [Field F] [NumberField F] (w : InfinitePlace F)
    (hw : w.IsReal) (φ : AdelicGL2 (𝓞 F) F → ℂ) : Prop :=
  ∀ g : AdelicGL2 (𝓞 F) F, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) fun z : UpperHalfPlane =>
    ((z.im : ℝ) : ℂ)⁻¹ * φ (g * adelicArchGLInclAt F w
      (Matrix.GeneralLinearGroup.map
        ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom)
        (iwasawaSectionGL z)))

def viaCompactCuspNotion : CuspidalityNotion (ℤ√(-2)) where
  IsCusp := fun F _i1 _i2 Φ =>
    (∃ R : SmoothCuspRealizationAt F (productionPinsCompact F)
        ((Φ.map iotaZsqrtdNegTwo).toRawCentral),
      (∀ w : InfinitePlace F, ∀ hw : w.IsReal,
        HasArchCharacterAt₀ F w (archWeightOneAt hw) R.toFun) ∧
      (∀ w : InfinitePlace F, ∀ hw : w.IsReal,
        IsArchHolomorphicAt w hw R.toFun)) ∧
    ∃ S : Finset (HeightOneSpectrum (𝓞 F)), ∀ v ∉ S,
      Φ.b v = ((chiNegThree (Ideal.absNorm v.asIdeal) : ℤ) : ℤ√(-2))

theorem viaCompactCuspNotion_isCusp_iff {F : Type} [Field F] [NumberField F]
    (Φ : HeckeEigensystem F (ℤ√(-2))) :
    viaCompactCuspNotion.IsCusp F Φ ↔
      (∃ R : SmoothCuspRealizationAt F (productionPinsCompact F)
          ((Φ.map iotaZsqrtdNegTwo).toRawCentral),
        (∀ w : InfinitePlace F, ∀ hw : w.IsReal,
          HasArchCharacterAt₀ F w (archWeightOneAt hw) R.toFun) ∧
        (∀ w : InfinitePlace F, ∀ hw : w.IsReal,
          IsArchHolomorphicAt w hw R.toFun)) ∧
      (∃ S : Finset (HeightOneSpectrum (𝓞 F)), ∀ v ∉ S,
        Φ.b v = ((chiNegThree (Ideal.absNorm v.asIdeal) : ℤ) : ℤ√(-2))) :=
  Iff.rfl

theorem isArithCuspRealizableVia_of_viaCompactCuspNotion {F : Type} [Field F]
    [NumberField F] (Φ : HeckeEigensystem F (ℤ√(-2)))
    (h : viaCompactCuspNotion.IsCusp F Φ) :
    IsArithCuspRealizableVia F (productionPinsCompact F) iotaZsqrtdNegTwo Φ :=
  ⟨h.1.choose⟩

end AutomorphicForm

end
