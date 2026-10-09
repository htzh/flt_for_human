/-
Push-forward and pull-back of Kähler differentials along an `K`-algebra map, and their
composite `Differential.correspondence`, after FLT's
`Definitions/Def_AlgebraicCurve_DifferentialPushPull.lean` (79 ln)
(<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DifferentialPushPull.lean>).

This is the differential-level analogue of `Defs/Correspondence.lean`'s divisor-level
`pullbackAlong`/`pushforwardAlong`/`correspondence`: `pullbackAlong φ` is
`KaehlerDifferential.map` restricted along `φ`, `traceAlong φ` is the trace of the
(separable) extension `F/F'`, and `correspondence φ ψ = traceAlong φ ∘ pullbackAlong ψ`.
It is the definition layer of `ModularCurve/Defs/HeckeDifferential.lean`'s `heckeDiffAlong`.

Statements are transcribed verbatim; the pin's `import Mathlib` is replaced by the
specific imports below, and its `import Definitions.Def_AlgebraicCurve_Correspondence`
by the ported `Defs.Correspondence` (which supplies `algebraAlong`,
`isScalarTower_along` and `SeparableAlong`).
-/
import FLTForHuman.AlgebraicCurve.Defs.Correspondence
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Trace.Defs
import Mathlib.RingTheory.TensorProduct.Maps

set_option autoImplicit false

-- The pin's `letI`/`haveI` walls are load-bearing: `pullbackAlong` unfolds only with the
-- local `Algebra F F'`/`IsScalarTower K F F'` instances in scope, and `traceAlong`'s
-- `dite` defeq needs the local `IsSeparable`/`FormallyEtale` binders (SET-1 §3). Keep them
-- literal rather than weaken the proofs.
set_option linter.style.haveILetI false

noncomputable section

open KaehlerDifferential TensorProduct

namespace AlgebraicCurve

namespace Differential

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

def pullbackAlong (φ : F →ₐ[K] F') : Ω[F⁄K] →ₗ[K] Ω[F'⁄K] :=
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  (KaehlerDifferential.map K K F F').restrictScalars K

theorem pullbackAlong_D (φ : F →ₐ[K] F') (f : F) :
    pullbackAlong φ (D K F f) = D K F' (φ f) := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  exact KaehlerDifferential.map_D K K F F' f

theorem pullbackAlong_smul (φ : F →ₐ[K] F') (f : F) (ω : Ω[F⁄K]) :
    pullbackAlong φ (f • ω) = φ f • pullbackAlong φ ω := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  show KaehlerDifferential.map K K F F' (f • ω) = _
  rw [LinearMap.map_smul_of_tower]
  rfl

open Classical in

def traceAlong (φ : F →ₐ[K] F') : Ω[F'⁄K] →ₗ[K] Ω[F⁄K] :=
  if h : SeparableAlong K φ then
    letI := algebraAlong φ
    haveI := isScalarTower_along φ
    haveI : Algebra.IsSeparable F F' := h
    haveI : Algebra.FormallyEtale F F' := Algebra.FormallyEtale.of_isSeparable F F'
    ((TensorProduct.lid F Ω[F⁄K]).toLinearMap ∘ₗ
      (Algebra.trace F F').rTensor Ω[F⁄K] ∘ₗ
      (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K F F').symm.toLinearMap).restrictScalars K
  else 0

theorem traceAlong_smul_pullbackAlong (φ : F →ₐ[K] F') (h : SeparableAlong K φ) (u : F')
    (ω : Ω[F⁄K]) :
    traceAlong φ (u • pullbackAlong φ ω) =
      (letI := algebraAlong φ; Algebra.trace F F' u) • ω := by
  letI := algebraAlong φ
  have := isScalarTower_along φ
  have : Algebra.IsSeparable F F' := h
  haveI : Algebra.FormallyEtale F F' := Algebra.FormallyEtale.of_isSeparable F F'
  rw [traceAlong, dite_eq_left h]
  simp only [LinearMap.coe_restrictScalars, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply]
  have hsymm : (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K F F').symm
      (u • pullbackAlong φ ω) = u ⊗ₜ ω := by
    rw [LinearEquiv.symm_apply_eq, KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply,
      KaehlerDifferential.mapBaseChange_tmul]
    rfl
  rw [hsymm, LinearMap.rTensor_tmul, TensorProduct.lid_tmul]

theorem traceAlong_of_not (φ : F →ₐ[K] F') (h : ¬ SeparableAlong K φ) : traceAlong φ = 0 := by
  rw [traceAlong, dite_eq_right h]

def correspondence (φ ψ : F →ₐ[K] F') : Ω[F⁄K] →ₗ[K] Ω[F⁄K] :=
  traceAlong φ ∘ₗ pullbackAlong ψ

theorem correspondence_apply (φ ψ : F →ₐ[K] F') (ω : Ω[F⁄K]) :
    correspondence φ ψ ω = traceAlong φ (pullbackAlong ψ ω) := rfl

end Differential

end AlgebraicCurve

end
